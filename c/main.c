#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Error codes
typedef enum {
    UTF8_OK = 0,
    UTF8_MORE,
    UTF8_INVALID_START_HEADER,
    UTF8_INVALID_CONTINUATION_HEADER,
    UTF8_CODEPOINT_TOO_BIG,
} utf8_decode_error;

// Byte ranges for DFA
typedef enum {
    RANGE_00_7F,
    RANGE_80_8F,
    RANGE_90_9F,
    RANGE_A0_BF,
    RANGE_C0_C1,
    RANGE_C2_DF,
    BYTE_E0,
    RANGE_E1_EC,
    BYTE_ED,
    RANGE_EE_EF,
    BYTE_F0,
    RANGE_F1_F3,
    BYTE_F4,
    RANGE_F5_FF
} byte_range_t;

// Parsing states
typedef enum {
    INITIAL,
    EXPECTING_1_80_BF,
    EXPECTING_2_80_BF,
    EXPECTING_3_80_BF,
    EXPECTING_2_80_9F,
    EXPECTING_2_A0_BF,
    EXPECTING_3_90_BF,
    EXPECTING_3_80_8F
} parsing_state_t;

// Result structure
typedef struct {
    bool finished;
    uint32_t codepoint;
    parsing_state_t state;
} parsing_result_t;

// Decode result
typedef struct {
    utf8_decode_error error;
    uint32_t *codepoints;
    size_t count;
    size_t bytes_consumed;
} utf8_decode_result_t;

// Determine byte range
byte_range_t get_byte_range(uint8_t b) {
    if (b <= 0x7F) return RANGE_00_7F;
    if (b <= 0x8F) return RANGE_80_8F;
    if (b <= 0x9F) return RANGE_90_9F;
    if (b <= 0xBF) return RANGE_A0_BF;
    if (b <= 0xC1) return RANGE_C0_C1;
    if (b <= 0xDF) return RANGE_C2_DF;
    if (b == 0xE0) return BYTE_E0;
    if (b <= 0xEC) return RANGE_E1_EC;
    if (b == 0xED) return BYTE_ED;
    if (b <= 0xEF) return RANGE_EE_EF;
    if (b == 0xF0) return BYTE_F0;
    if (b <= 0xF3) return RANGE_F1_F3;
    if (b == 0xF4) return BYTE_F4;
    return RANGE_F5_FF;
}

// Push bottom 6 bits of byte into codepoint (left shift by 6, then OR)
uint32_t push_bottom_bits(uint32_t carry, uint8_t b) {
    return (carry << 6) | (b & 0x3F);
}

// Extract bits for different UTF-8 byte types
uint32_t extract_7_bits(uint8_t b) {
    return b & 0x7F;
}

uint32_t extract_5_bits(uint8_t b) {
    return b & 0x1F;
}

uint32_t extract_4_bits(uint8_t b) {
    return b & 0x0F;
}

uint32_t extract_3_bits(uint8_t b) {
    return b & 0x07;
}


// Core DFA state transition function
utf8_decode_error next_state(
    uint8_t b,
    parsing_state_t* state,
    uint32_t* codepoint
) {
    byte_range_t range = get_byte_range(b);
    
    parsing_state_t state_value = *state;
    switch (state_value) {
    case INITIAL:
        switch (range) {
        case RANGE_00_7F:
            *codepoint = extract_7_bits(b);
            return UTF8_OK;
        case RANGE_C2_DF:
            *state = EXPECTING_1_80_BF;
            *codepoint = extract_5_bits(b);
            return UTF8_MORE;
        case BYTE_E0:
            *state = EXPECTING_2_A0_BF;
            *codepoint = extract_4_bits(b);
            return UTF8_MORE;
        case RANGE_E1_EC:
        case RANGE_EE_EF:
            *state = EXPECTING_2_80_BF;
            *codepoint = extract_4_bits(b);
            return UTF8_MORE;
        case BYTE_ED:
            *state = EXPECTING_2_80_9F;
            *codepoint = extract_4_bits(b);
            return UTF8_MORE;
        case BYTE_F0:
            *state = EXPECTING_3_90_BF;
            *codepoint = extract_3_bits(b);
            return UTF8_MORE;
        case RANGE_F1_F3:
            *state = EXPECTING_3_80_BF;
            *codepoint = extract_3_bits(b);
            return UTF8_MORE;
        case BYTE_F4:
            *state = EXPECTING_3_80_8F;
            *codepoint = extract_3_bits(b);
            return UTF8_MORE;
        default:
            return UTF8_INVALID_START_HEADER;
        }
        
    case EXPECTING_1_80_BF:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
        case RANGE_A0_BF:
            *state = INITIAL;
            uint32_t codepoint_value = *codepoint;
            *codepoint = push_bottom_bits(codepoint_value, b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_2_80_BF:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
        case RANGE_A0_BF:
            *state = EXPECTING_1_80_BF;
            uint32_t codepoint_value = *codepoint;
            *codepoint = push_bottom_bits(codepoint_value, b);
            return UTF8_MORE;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_2_80_9F:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
            *state = EXPECTING_1_80_BF;
            uint32_t codepoint_value = *codepoint;
            *codepoint = push_bottom_bits(codepoint_value, b);
            return UTF8_MORE;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_2_A0_BF:
        switch (range) {
        case RANGE_A0_BF:
            *state = EXPECTING_1_80_BF;
            uint32_t codepoint_value = *codepoint;
            *codepoint = push_bottom_bits(codepoint_value, b);
            return UTF8_MORE;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_3_80_BF:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
        case RANGE_A0_BF:
            *state = EXPECTING_2_80_BF;
            uint32_t codepoint_value = *codepoint;
            *codepoint = push_bottom_bits(codepoint_value, b);
            return UTF8_MORE;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_3_90_BF:
        switch (range) {
        case RANGE_90_9F:
        case RANGE_A0_BF:
            *state = EXPECTING_2_80_BF;
            uint32_t codepoint_value = *codepoint;
            *codepoint = push_bottom_bits(codepoint_value, b);
            return UTF8_MORE;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_3_80_8F:
        switch (range) {
        case RANGE_80_8F:
            *state = EXPECTING_2_80_BF;
            uint32_t codepoint_value = *codepoint;
            *codepoint = push_bottom_bits(codepoint_value, b);
            return UTF8_MORE;
        case RANGE_90_9F:
        case RANGE_A0_BF:
            return UTF8_CODEPOINT_TOO_BIG;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
    }
    
    return UTF8_INVALID_CONTINUATION_HEADER;
}

utf8_decode_error next_codepoint(uint8_t** cursor, uint8_t* end, uint32_t* codepoint_out) {
    parsing_state_t state = INITIAL;
    *codepoint_out = 0;
    utf8_decode_error result;
    uint8_t* cursor_value = *cursor;
    while (cursor_value < end) {
        uint8_t b = *cursor_value;
        result = next_state(b, &state, codepoint_out);
        
        cursor_value++;
        if (result != UTF8_MORE) {
            break;
        }
    }
    *cursor = cursor_value;
    return result;
}

// Example usage and test function
void print_codepoint(const uint32_t codepoint) {
    printf("U+%04X ", codepoint);
}

void print_codepoints(uint8_t* text, size_t size) {
    uint8_t* end = text+size;
    uint32_t codepoint;
    while (text < end) {
        next_codepoint(&text, end, &codepoint);
        print_codepoint(codepoint);
    }
    printf("\n");
}

int main() {
    // Test with various UTF-8 sequences
    uint8_t test1[] = "Hello"; // ASCII
    uint8_t test2[] = {0xC3, 0xA9}; // é (U+00E9)
    uint8_t test3[] = {0xE2, 0x82, 0xAC}; // € (U+20AC)
    uint8_t test4[] = {0xF0, 0x9F, 0x98, 0x80}; // 😀 (U+1F600)
    
    print_codepoints(test1, sizeof(test1));
    print_codepoints(test2, sizeof(test2));
    print_codepoints(test3, sizeof(test3));
    print_codepoints(test4, sizeof(test4));
    
    return 0;
}
