#import "template.typ": project

#show: project.with(
    title: "Verificação formal de uma implementação eficiente de um decodificador de UTF-8",
    authors: ((
        name: "Leonardo Santiago",
        email: "leonardors@dcc.ufrj.br",
        affiliation: "UFRJ",
    ),),
    abstract: [O sistema de codificação #emph("Unicode") é imprescindível para a comunicação global, permitindo que inúmeras linguagens utilizem a mesma representação para transmitir todas os caracteres, eliminando a necessidade de conversão. Três formatos para serializar #emph("codepoints") em bytes existem, UTF-8, UTF-16 e UTF-32; entretanto, o formato mais ubíquito é UTF-8, pela sua retro compatibilidade com ASCII, e a capacidade de economizar bytes. Apesar disso, vários problemas aparecem ao implementar um programa codificador e decodificador de UTF-8 semânticamente correto, e inúmeras vulnerabilidades estão associadas a isso. Neste trabalho será utilizada verificação formal através de tipos dependentes, não apenas para enumerar todas as propriedades dadas na especificação do UTF-8, mas principalmente para desenvolver implementações e provar que estas estão corretasg. Primeiro, uma implementação simplificada será desenvolvida, focando em provar todas as propriedades, depois uma implementação focada em eficiência e performance será dada, junto com provas de que as duas são equivalentes, e por fim essa implementação será extraída para um programa executável.]
)

= Introdução
// https://speakerdeck.com/alblue/a-brief-history-of-unicode?slide=7
// https://www.unwoundstack.com/blog/testing-poor-substitute-for-reasoning.html
// https://www.unwoundstack.com/blog/type-theory.html
// https://vladris.com/blog/2018/11/18/notes-on-encoding-text.html
// https://tonsky.me/blog/unicode/
// https://en.wikipedia.org/wiki/Han_unification

O processo de desenvolvimento de software pode ser separado em dois problemas distintos: o de validação, que pretende assegurar que o programa a ser desenvolvido resolve um problema desejado, e o de verificação, que assegura que o programa desenvolvido implementa as especificações formadas na fase de validação.

Validação é tópico de estudo das práticas de modelagem de software, que tem como produção gráficos conceituais, modelos e regras de negócio, que devem ser utilizados para desenvolver o programa.

Dessa forma, verificação formal de software descreve o conjunto de axiomas, regras e práticas que permitem construir provas sobre o comportamento de programas de computador. Através do formalismo matemático, torna-se possível conferir a um software fortes garantias de corretude, assegurando-se que está conforme as especificações.

O compilador de C _CompCert_ (@2006-Leroy-compcert) é um dos maiores expoentes dessa área. Ao desenvolver um modelo formal de memória contendo ponteiros, o compilador permite não somente descrever transformações entre programas, mas também provar matematicamente que tais transformações preservam a semântica do programa original. Dessa forma, torna-se trivial introduzir otimizações que simplificam o programa, garantindo que essas não introduzem _bugs_ no programa original. De fato, @Yang2011 mostraram que, dentre todos os compiladores de C tradicionais, incluindo `gcc` e `clang`, o _CompCert_ fora o único a não apresentar sequer um _bug_ de compilação após testes minuciosos.

O microkernel _seL4_ (@Klein2014) é o primeiro e único microkernel de propósito geral que possue uma prova de corretude de funcionalidade, isto é, que seu código em _C_ implementa o modelo abstrato de sua especificação, o que o torna livre de problemas de _stack overflow_, _deadlocks_, erros de aritmética e outros problemas de implementação. Além disso, provas de garantia de disponibilidade, integridade, e performance no pior caso são todas formalmente verificadas, fazendo com que esse micro-kernel tenha ampla adoção em casos de uso de missão crítica.

O algoritmo de consenso _Raft_ é um exemplo de algoritmo implementado utilizando bases de verificação formal, sendo desenvolvido com base na lógica de separação, oferencendo garantias de segurança, disponibilidade e corretude, sendo adotado por inúmeras implementações de bancos de dados, como _ScyllaDB_, _MongoDB_, _ClickHouse_, _Apache Kafka_, e muitos outros.

Além de útil para produção de software e algoritmos corretos, as ferramentas de verificação formal são ótimos fundamentos para o desenvolvimento da matemática. @FourColorTheorem completamente formalizaram a prova do teorema das 4 cores no provador interativo Coq, cuja prova inicial, por @Appel1977, era extremamente complicada e sofria críticas por sua complexidade. @Gonthier2013 formalizaram o teorema de Feit-Thompson, cuja prova manual contém mais de 10 mil páginas. Mais recentemente, em 2024, o valor de $"BusyBeaver"(5)$ fora calculado como $47.176.870$ utilizando Coq (@BBchallenge2024), cujo processo consiste em decidir dentre todas as máquinas de Turing de tamanho 5 que terminam, a que leva o maior número de passos para terminar.

Assim, este trabalho tem o objetivo de utilizar a linguagem Coq para desenvolver um programa que le bytes no padrão UTF-8 e formalizar uma prova de que esse programa não aceita bytes inválidos de acordo com a especificação. Isso será feito através de dois programas complementares, um que aceita bytes e retorna _codepoints_ (decodificador), e seu programa dual, que aceita _codepoints_ e retorna _bytes_ (codificador). Além provar propriedades importantes sobre cada um dos programas, o cerne da corretude está na prova de que todo resultado válido de um dos programas é aceito corretamente pelo outro.

Performance e eficiência do programa final também serão considerados, com o objetivo de mostrar que não é necessario descartar a eficiência para obter um programa correto. Para tal, uma implementação do codificador baseada em autômatos finitos será desenvolvida, bem como uma prova de que esse é exatamente equivalente ao codificador original correto.

= Trabalhos relacionados

= Unicode

// https://tonsky.me/blog/unicode/
// https://www.joelonsoftware.com/2003/10/08/the-absolute-minimum-every-software-developer-absolutely-positively-must-know-about-unicode-and-character-sets-no-excuses

Sistemas antigos de codificação de caracteres tradicionalmente utilizam um mapeamento um pra um entre caracteres e bytes, tanto por simplicidade de codificação quanto por eficiência de armazenamento de memória. Programas que decodificam bytes em caracteres nesses sistemas antigos são extremamente simples, e podem ser resumidos a tabelas de conversão direta, conhecidas como _code pages_.

Representar um byte por caractere coloca uma severa limitação no número de caracteres que conseguem expressar ($<= 256$), fazendo com que cada linguagem diferente tivesse sua própria maneira distinta de representar seus caracteres, e que muitas vezes era incompatível com outras famosas. Assim, enviar textos pela internet era uma tarefa extremamente complicada, visto que não era garantido que o usuário que recebe a mensagem teria as tabelas necessárias para decodificá-la corretamente.

Para piorar a situação, linguagens baseadas em ideogramas, como japonês, coreano e chinês, possuem milhares de caracteres, e codificá-las em apenas um byte é impossível. Tais linguagens foram pioneiras em encodings multi-bytes, em que um caractere é transformado em mais de um byte, tornando a codificação e decodificação significativamente mais complexa.

O padrão Unicode fora criado então para que um único sistema de codificação consiga cobrir todas as linguagens, com todos seus caracteres específicos, de forma que qualquer texto escrito em qualquer linguagem possa ser escrito nele. Apesar de extremamente ambicioso, esse sistema rapidamente ganhou adoção mundial, massivamente simplificando a comunicação na internet.

== UCS-2 e UTF-16

Para entender a razão por trás do formato moderno do Unicode, faz-se necessário entender a história por trás de sua criação. Em 1991, a versão 1.0 do Unicode fora lançado como uma codificação de tamanho fixo de 16 bits, chamada de UCS-2 -- _Universal Coding System_ -- capaz de representar 65536 caracteres, chamados de _code points_, das mais diversas línguas.

Tal quantidade, apesar de muito maior do que os antigos 256, rapidamente provou-se não suficiente para todas as linguagens. Quando isso fora percebido, o sistema UCS-2 já estava em amplo uso, e trocá-lo por outro sistema já não era mais possível. Assim, para estendê-lo mantendo-o retro compatível, decidiram reservar parte da tabela para que dois _code points_ distintos (32 bits) representem um único _code point_, isto é, pares de _code units_, denominados _surrogate pairs_, representando um único caractere. Dessa forma, o sistema deixou de ter um tamanho fixo de 16 bits, e passou a ter um tamanho variável, dependendo de quais _code points_ são codificados.

// https://en.wikipedia.org/wiki/UTF-16

O padrão UCS-2 estendido com _surrogate pairs_ é o padrão conhecido como UTF-16, que rapidamente obteve adoção de sistemas de grande relevância, como as linguagens Java e JavaScript, o sistema de UI Qt e até mesmo as APIs do Windows.

Para determinar se uma sequência de bytes é válida em UTF-16, faz se necessário determinar se os dois primeiros bytes representam o início de um _surrogate pair_, representado por bytes entre `D800` e `DBFF`, seguido de bytes que representam o fim de um _surrogate pair_, entre `DC00` e `DFFF`. 
#align(center,```
      High Surrogate          Low Surrogate
        D800..DBFF               DC00..DFFF
   byte 1      byte 2      byte 3      byte 4    
| 1101 10?? | ???? ???? | 1101 11?? | ???? ???? |
```)

Iniciar um _surrogate pair_ (`D800..DBFF`) e não terminá-lo com um byte no intervalo correto (`DC00..DFFF`) é considerado um erro, e é inválido segundo a especificação. Assim, determinar se uma sequência de bytes deixou de ser uma tarefa trivial, e tornou-se um possível lugar onde erros de segurança podem acontecer. De fato, CVE-2008-2938 e CVE-2012-2135 são exemplos de vulnerabilidades encontradas em funções relacionadas à decodificação em UTF-16, em projetos grandes e bem estabelecidas (python e APACHE, respectivamente).

Assim, o sistema UTF-16, e consequentemente o próprio Unicode, consegue expressar $1.112.064$ _code points_. Esse número pode ser enxergado da seguinte forma:
#align(center, table(columns: (auto, auto, auto),
    stroke: none,
    table.header("Intervalo", "Tamanho", "Descrição"),
    `U+0000..U+FFFF`, $2^16$, "Basic Multilingual Plane, Plane 0",
    `U+D800..U+DFFF`, $2^11$, "Surrogate Pairs",
    `U+10000..U+10FFFF`, $2^20$, "Higher Planes, Planes 1-16",
    table.hline(), 
    `U+0000..U+10FFFF`, $2^20 + 2^16 - 2^11$, "Codepoints representáveis"
))

O padrão Unicode explicita que *nenhum* _code point_ pode ser representado pelo intervalo `U+D800..U+DFFF`, de forma que todos os outros sistemas de codificação -- UTF-8, UTF-32 -- tenham que desenvolver sistemas para evitar que esses sejam considerados _code points_ válidos.

Vale notar que há ambiguidade na forma de serializar UTF-16 para bytes, visto que não é especificado se o primeiro byte de um _code point_ deve ser o mais significativo -- Big Endian -- ou o menos significativo -- Little Endian. Para distinguir, é comum o uso do caractere `U+FEFF`, conhecido como _Byte Order Mark_ (BOM), como o primeiro caractere de uma mensagem ou arquivo. No caso de Big Endian, o BOM aparece como `FEFF`, e no caso de Little Endian, aparece como `FFFE`.

Essa distinção é o que faz com que UTF-16 possa ser divido em duas sub linguagens, UTF-16BE (Big Endian) e UTF-16LE (Little Endian), adicionando ainda mais complexidade à tarefa de codificar e decodificar os caracteres corretamente.

Apesar de extremamente útil, o UTF-16 utiliza 2 bytes para cada caractere, então não é eficiente para linguagens que utilizam ASCII (1 byte por caractere), bem como para formatos como HTML e JSON utilizados na internet, que usam muitos caracteres nos primeiros 127 _code points_ -- `<`, `>`, `{`, `:`. Por isso, fez-se necessário achar outra forma de codificá-los que fosse mais eficiente para a comunicação digital.

== UTF-8

Criado por Rob Pike e Ken Thompson, o UTF-8 surgiu como uma alternativa ao UTF-16 mais eficiente, ao representar os primeiros 127 _code points_ exatamente igual a ASCII. A principal mudança para que isso fosse possível foi de abandonar a ideia de codificação de tamanho fixo, que imensamente facilita escrever os programas, para uma codificação de tamanho variável.

A quantidade de bytes necessárias para representar um _code point_ em UTF-8 é uma função do intervalo que esse _code point_ se encontra. Considerando que um _code point_ tem 21 bits de conteúdo, podemos separá-lo em `u, vvvv, wwww, xxxx, yyyy, zzzz`, onde cada variável representa 1 bit. Utilizando essa notação, a serialização deste pode ser vista como:

#align(center, table(columns: (auto, auto, auto),
    align: (auto, right, auto),
    stroke: none,
    table.header("Intervalo", "Bytes", "Bits relevantes"),
    `U+0000..U+007F`, `0yyyzzzz`, "7 bits",
    `U+0080..U+07FF`, `110xxxyy 10yyzzzz`, "11 bits",
    `U+0800..U+FFFF`, `1110wwww 10xxxxyy 10yyzzzz`, "16 bits",
    `U+10000..U+10FFFF`, `11110uvv 10vvwwww 10xxxxyy 10yyzzzz`, "21 bits",
))

É importante notar que os primeiros 127 bits são representados exatamente igual caracteres ASCII (#text(fill:red, "e sistemas extendidos")), algo extremamente desejável não apenas para retro compatibilidade com sistemas antigos, mas para recuperar parte da eficiência de espaço, perdida no UTF-16.




// https://nvd.nist.gov/vuln/detail/CVE-2008-2938
// https://nvd.nist.gov/vuln/detail/CVE-2012-2135




#bibliography("references.bib", style: "associacao-brasileira-de-normas-tecnicas")
