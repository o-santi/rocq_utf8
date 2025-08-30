#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Error codes
typedef enum {
    UTF8_OK = 0,
    UTF8_INVALID_START_HEADER,
    UTF8_INVALID_CONTINUATION_HEADER,
    UTF8_CODEPOINT_TOO_BIG
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
static byte_range_t get_byte_range(uint8_t b) {
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
static uint32_t push_bottom_bits(uint32_t carry, uint8_t b) {
    return (carry << 6) | (b & 0x3F);
}

// Extract bits for different UTF-8 byte types
static uint32_t extract_7_bits(uint8_t b) {
    return b & 0x7F;
}

static uint32_t extract_5_bits(uint8_t b) {
    return b & 0x1F;
}

static uint32_t extract_4_bits(uint8_t b) {
    return b & 0x0F;
}

static uint32_t extract_3_bits(uint8_t b) {
    return b & 0x07;
}

// Core DFA state transition function
static utf8_decode_error next_state(parsing_state_t state, uint32_t carry, uint8_t b,
                                   parsing_result_t *result) {
    byte_range_t range = get_byte_range(b);
    
    switch (state) {
    case INITIAL:
        switch (range) {
        case RANGE_00_7F:
            result->finished = true;
            result->codepoint = extract_7_bits(b);
            return UTF8_OK;
        case RANGE_C2_DF:
            result->finished = false;
            result->state = EXPECTING_1_80_BF;
            result->codepoint = extract_5_bits(b);
            return UTF8_OK;
        case BYTE_E0:
            result->finished = false;
            result->state = EXPECTING_2_A0_BF;
            result->codepoint = extract_4_bits(b);
            return UTF8_OK;
        case RANGE_E1_EC:
        case RANGE_EE_EF:
            result->finished = false;
            result->state = EXPECTING_2_80_BF;
            result->codepoint = extract_4_bits(b);
            return UTF8_OK;
        case BYTE_ED:
            result->finished = false;
            result->state = EXPECTING_2_80_9F;
            result->codepoint = extract_4_bits(b);
            return UTF8_OK;
        case BYTE_F0:
            result->finished = false;
            result->state = EXPECTING_3_90_BF;
            result->codepoint = extract_3_bits(b);
            return UTF8_OK;
        case RANGE_F1_F3:
            result->finished = false;
            result->state = EXPECTING_3_80_BF;
            result->codepoint = extract_3_bits(b);
            return UTF8_OK;
        case BYTE_F4:
            result->finished = false;
            result->state = EXPECTING_3_80_8F;
            result->codepoint = extract_3_bits(b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_START_HEADER;
        }
        
    case EXPECTING_1_80_BF:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
        case RANGE_A0_BF:
            result->finished = true;
            result->codepoint = push_bottom_bits(carry, b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_2_80_BF:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
        case RANGE_A0_BF:
            result->finished = false;
            result->state = EXPECTING_1_80_BF;
            result->codepoint = push_bottom_bits(carry, b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_2_80_9F:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
            result->finished = false;
            result->state = EXPECTING_1_80_BF;
            result->codepoint = push_bottom_bits(carry, b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_2_A0_BF:
        switch (range) {
        case RANGE_A0_BF:
            result->finished = false;
            result->state = EXPECTING_1_80_BF;
            result->codepoint = push_bottom_bits(carry, b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_3_80_BF:
        switch (range) {
        case RANGE_80_8F:
        case RANGE_90_9F:
        case RANGE_A0_BF:
            result->finished = false;
            result->state = EXPECTING_2_80_BF;
            result->codepoint = push_bottom_bits(carry, b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_3_90_BF:
        switch (range) {
        case RANGE_90_9F:
        case RANGE_A0_BF:
            result->finished = false;
            result->state = EXPECTING_2_80_BF;
            result->codepoint = push_bottom_bits(carry, b);
            return UTF8_OK;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
        
    case EXPECTING_3_80_8F:
        switch (range) {
        case RANGE_80_8F:
            result->finished = false;
            result->state = EXPECTING_2_80_BF;
            result->codepoint = push_bottom_bits(carry, b);
            return UTF8_OK;
        case RANGE_90_9F:
        case RANGE_A0_BF:
            return UTF8_CODEPOINT_TOO_BIG;
        default:
            return UTF8_INVALID_CONTINUATION_HEADER;
        }
    }
    
    return UTF8_INVALID_CONTINUATION_HEADER;
}

// Main UTF-8 decoder function
utf8_decode_result_t utf8_dfa_decode(const uint8_t *bytes, size_t len) {
    utf8_decode_result_t result = {0};
    
    if (!bytes || len == 0) {
        result.error = UTF8_OK;
        return result;
    }
    
    // Allocate maximum possible codepoints (worst case: all ASCII)
    uint32_t *codepoints = malloc(len * sizeof(uint32_t));
    if (!codepoints) {
        result.error = UTF8_INVALID_START_HEADER; // Use as generic error
        return result;
    }
    
    size_t pos = 0;
    size_t cp_count = 0;
    parsing_state_t state = INITIAL;
    uint32_t carry = 0;
    
    while (pos < len) {
        parsing_result_t parse_result;
        utf8_decode_error error = next_state(state, carry, bytes[pos], &parse_result);
        
        if (error != UTF8_OK) {
            free(codepoints);
            result.error = error;
            result.bytes_consumed = pos;
            return result;
        }
        
        if (parse_result.finished) {
            codepoints[cp_count++] = parse_result.codepoint;
            state = INITIAL;
            carry = 0;
        } else {
            state = parse_result.state;
            carry = parse_result.codepoint;
        }
        
        pos++;
    }
    
    // Check if we ended in a valid state
    if (state != INITIAL) {
        free(codepoints);
        result.error = UTF8_INVALID_CONTINUATION_HEADER;
        result.bytes_consumed = pos;
        return result;
    }
    
    // Resize to actual count
    if (cp_count > 0) {
        uint32_t *final_codepoints = realloc(codepoints, cp_count * sizeof(uint32_t));
        result.codepoints = final_codepoints ? final_codepoints : codepoints;
    } else {
        free(codepoints);
        result.codepoints = NULL;
    }
    
    result.count = cp_count;
    result.bytes_consumed = pos;
    result.error = UTF8_OK;
    return result;
}

// Helper function to free decode result
void utf8_decode_result_free(utf8_decode_result_t *result) {
    if (result && result->codepoints) {
        free(result->codepoints);
        result->codepoints = NULL;
        result->count = 0;
    }
}

// Example usage and test function
void print_codepoints(const utf8_decode_result_t *result) {
    if (result->error != UTF8_OK) {
        printf("Error: %d at byte position %zu\n", result->error, result->bytes_consumed);
        return;
    }
    
    printf("Decoded %zu codepoints: ", result->count);
    for (size_t i = 0; i < result->count; i++) {
        printf("U+%04X ", result->codepoints[i]);
    }
    printf("\n");
}

int main() {
    // Test with various UTF-8 sequences
    const uint8_t test1[] = "Hello"; // ASCII
    const uint8_t test2[] = {0xC3, 0xA9}; // é (U+00E9)
    const uint8_t test3[] = {0xE2, 0x82, 0xAC}; // € (U+20AC)
    const uint8_t test4[] = {0xF0, 0x9F, 0x98, 0x80}; // 😀 (U+1F600)
    
    utf8_decode_result_t result1 = utf8_dfa_decode(test1, 5);
    print_codepoints(&result1);
    utf8_decode_result_free(&result1);
    
    utf8_decode_result_t result2 = utf8_dfa_decode(test2, 2);
    print_codepoints(&result2);
    utf8_decode_result_free(&result2);
    
    utf8_decode_result_t result3 = utf8_dfa_decode(test3, 3);
    print_codepoints(&result3);
    utf8_decode_result_free(&result3);
    
    utf8_decode_result_t result4 = utf8_dfa_decode(test4, 4);
    print_codepoints(&result4);
    utf8_decode_result_free(&result4);
    
    return 0;
}
