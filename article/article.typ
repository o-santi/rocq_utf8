#import "template.typ": project, hex

#set raw(syntaxes: "Coq.sublime-syntax")

#show: project.with(
    title: "Verificação formal de uma implementação eficiente de um decodificador de UTF-8",
    authors: ((
        name: "Leonardo Santiago",
        email: "leonardors@dcc.ufrj.br",
        affiliation: "UFRJ",
    ),),
    abstract: [O sistema de codificação #emph("Unicode") é imprescindível para a comunicação global, permitindo que inúmeras linguagens utilizem a mesma representação para transmitir todas os caracteres, eliminando a necessidade de conversão. Dentre todos os formatos de serializar caracteres do Unicode - denominados #emph("codepoints") - certamente o formato mais ubíquito é o UTF-8, pela sua retro compatibilidade com ASCII, e a capacidade de economizar bytes. Apesar de ser utilizado em mais de 98% das páginas da internet, vários problemas aparecem ao implementar programas de codificação e decodificaçãos de UTF-8 semânticamente corretos, e inúmeras vulnerabilidades estão associadas a esse processo. Dificultando ainda mais, a especificação dada pelo Consórcio Unicode é feita inteiramente em prosa, tornando extremamente difícil afirmar com segurança que dada implementação respeita-a por métodos tradicionais. Assim, este trabalho utilizará verificação formal através de provadores de teoremas interativos com dois propósitos. Primeiro, será desenvolvido um conjunto de propriedades - a especificação - que unicamente representam um par de programas codificador e decodificador de UTF-8. Com a especificação formalizada, serão implementados um codificador e decodificador, mostrando que esses respeitam todas as propriedades necessárias para que estejam corretos. ]
)

= Introdução
// https://speakerdeck.com/alblue/a-brief-history-of-unicode?slide=7
// https://www.unwoundstack.com/blog/testing-poor-substitute-for-reasoning.html
// https://www.unwoundstack.com/blog/type-theory.html
// https://vladris.com/blog/2018/11/18/notes-on-encoding-text.html
// https://tonsky.me/blog/unicode/
// https://en.wikipedia.org/wiki/Han_unification

O processo de desenvolvimento de software pode ser separado em duas fases distintas: a de validação, que pretende desenvolver especificações necessárias para que um programa resolva um problema no mundo real, e a de verificação, que assegura que o programa desenvolvido implementa essas especificações.

Especificação é o principal tópico de estudo das práticas de modelagem de software, que tem como produção gráficos conceituais, modelos e regras de negócio, que devem ser utilizados para desenvolver o programa. O objetivo dessas é gerar um conjunto de objetivos e propriedades que programas devem satisfazer para que atinjam algum fim no mundo real, conferindo semântica à resultados e implementações, e construindo pontes tangíveis entre modelos teóricos e a realidade prática.

Assegurar que dada implementação segue as regras de negócio geradas na fase de especificação é tópico de estudo da área de verificação. Dela, inúmeras práticas comuns na área de programação são derivadas, como desenvolvimento de testes, garantias de qualidade e checagens de tipo. Apesar das inúmeras práticas, preencher a lacuna entre a semântica dos modelos teóricos e as implementações em código é extremamente difícil, dada a natureza das práticas tradicionais baseadas em testes unitários. Testes oferecem visões circunstanciais do comportamento do programa a partir de certas condições iniciais, tornando impossível assegurar com totalidade a corretude do programa, visto que programas complexos teriam de ter um número impraticável de testes  -- muitas vezes infinito -- para checar todas as combinações de condições iniciais.

É cotidiano que erros passem desapercebidos por baterias gigantescas de testes e apareçam somente em produção -- quando erros são inaceitáveis -- em especial quando ocorrem em combinações muito específicas de entrada. Muitas linguagens então tomam uma abordagem dinâmica, isto é, tornar erros mais fáceis de serem detectados adicionando inúmeras checagens enquanto o programa executa, e tornando-o programa ainda mais sucetível a erros. Para atingir _software_ correto, é imprescindível a análise estática dos programas, mas técnicas comuns de análise estática não são potentes o suficiente para conferir segurança e corretude, e são mais complexas do que abordagens dinâmicas.

Verificação formal de software denomina a área da verificação que oferece diretrizes para raciocinar formalmente sobre um programa, descrevendo axiomas, regras e práticas que permitem construir provas sobre o comportamento desse. Ao estruturar o programa para permitir o raciocínio matemático, torna-se possível atribuir uma semântica a um software, conferindo fortes garantias de corretude, e assegurando-se que esse está conforme as especificações da semântica. Para auxiliar nesse processo, várias ferramentas foram desenvolvidas, como _model checkers_, que tentam gerar provas automaticamente a partir de modelos fornecidos, e provadores de teorema interativos, que permitem o desenvolvedor de elaborar provas sobre programas utilizando linguagens específicas para construí-las.

Por necessitar que programas sejam estruturados de maneira a facilitar o raciocínio lógico, a metodologia da verificação formal dificilmente é aplicada a projetos complexos já existentes, visto que tradicionalmente são feitos com outros objetivos em mente -- facilidade de desenvolvimento, agilidade em desenvolver novas capacidades, ou até mesmo velocidade do programa gerado. Além disso, as ferramentas mais poderosas de verificação formal, os provadores de teoremas interativos, utilizam tipos dependentes, que nativamente utilizam linguagens funcionais para sua lógica interna, o que significa que expressar programas imperativos nessas geralmente requer muito mais trabalho. Assim, fica claro que existem certas barreiras para a adoção de métodos formais na indústria.

O objetivo deste trabalho é, portanto, documentar os benefícios, bem como as dificuldades, da aplicação desses métodos a problemas suficientemente complexos, de forma a confirmar ou refutar o estigma existente na adoção da verificação formal. Em particular, o problema da codificação e decodificação de caracteres em UTF-8 fora escolhido pela sua difusão em praticamente todos os contextos e linguagens de programação.

O padrão Unicode (@unicode) de representação de caracteres é ubíquito na comunicação na internet, e seu principal formato de codificação e decodificação, UTF-8, é utilizado em mais de 98% das páginas web (@Utf8Usage2025). Apesar disso, inúmeras CVEs estão associadas a programas que tratam UTF-8 incorretamente, especialmente por não implementarem totalmente a especificação, visto que muitos casos incomuns podem acabar sendo esquecidos.

As vulnerabilidades CVE-2000-0884 (Microsoft IIS) e CVE-2008-2938 (APACHE Tomcat) estão diretamente associadas à má gestão de input ao ler caracteres UTF-8, permitindo ao atacante de ler arquivos em caminhos fora do inicialmente permitido (ataque conhecido como _directory traversal_). A CVE-2004-2579 (Novell iChain) está associada a um ataque que utiliza representações ilegais de caracteres de escape em UTF-8 para ultrapassar regras de controle. A CVE-2007-6284 (libxml2) permite que ataques de negação de serviço (/loops/ infinito) através da utilização de caracteres mal formados em textos XML.

// https://github.com/JuliaStrings/utf8proc/tree/master

// https://discourse.julialang.org/t/bug-in-isvalid-with-an-overlong-utf-8-encoded-vector-or-string/15290 & https://github.com/JuliaLang/julia/issues/11141

// https://github.com/python/cpython/blob/da7f4e4b22020cfc6c5b5918756e454ef281848d/Parser/tokenizer/helpers.c#L447

// https://unicodebook.readthedocs.io/issues.html#non-strict-utf-8-decoder-overlong-byte-sequences-and-surrogates

// https://www.cve.org/CVERecord?id=CVE-2007-6284

// https://github.com/bminor/glibc/blob/91fb9914d867320d65a2abe284fb623d91ae5efb/iconvdata/tst-table-from.c#L110 função na glibc que aceita utf8 de até 6 caracteres + overlongs.

// https://unicodebook.readthedocs.io/programming_languages.html#c-language

Não apenas programas específicos estão sujeitos a erros na implementação, mas até mesmo implementações básicas em linguagens difundidas cometem erros cruciais. O leitor de UTF-8 da linguagem PHP em versões mais antigas não tratava corretamente casos especiais desse sistema, tornando possível injeções de SQL (CVE-2009-4142), _cross site scripting_ (CVE-2010-3870), e _integer overflows_ (CVE-2009-5016). Até mesmo a linguagem Julia, criada em 2012 -- anos depois da consolidação do sistema Unicode -- apresentou problemas de decodificação de sequências inválidas UTF-8. Dessa forma, fica claro que a formalização formal como forma de assegurar corretude e segurança é uma ferramenta valiosa.

Este trabalho é estruturado nas seguintes seções:
1. Na seção 2, a história por trás do sistema Unicode será revista, com o objetivo de motivar a estruturação atual dos sistemas de codificação UTF-8, UTF-16 e UTF-32, bem como algumas de suas propriedades e  limitações. Também será inspecionada a literatura existente, tanto especificações existentes do Unicode quanto sobre abordagens e metodologias tradicionais de provar formalmente a corretude de codificadores e decodificadores de linguagens.
3. Na seção 3, será elaborado um conjunto de regras formais que um codificador e decodificador, denominado de *especificação*, e serão provados teoremas que fundamentam a corretude desse. Para auxiliar na prova de teoremas, é desenvolvida uma teoria sobre isomorfismos em conjuntos finitos.
4. Na seção 4, serão desenvolvidos implementações práticas de um codificador e decodificador UTF-8, levando em consideração fatores como simplicidade, utilidade e eficiência, de maneira similar a como são implementados em linguagens "imperativas".
5. Na seção 5, serão dadas as considerações finais, bem como aplicações naturais desse trabalho para cenários práticos.

Neste trabalho estão contidas as seguintes contribuições:

1. A primeira prova formal de que há um mapeamento único entre o formato oficial de bytes UTF-8 e codepoints válidos, isto é, que a especificação do Unicode está correta.
2. Um conjunto de regras formais para decidir automaticamente se dado codificador ou decodificador respeita o formato UTF-8, junto de provas de corretude sobre esse conjunto de regras, de forma a motivar sua relevância. Em especial, é utilizada uma abordagem inovadora utilizando funções crescentes para completamente descrever a codificação UTF-8.
3. Uma implementação formalmente correta, no sentido das regras supracitadas, de tanto um codificador quanto decodificador.

#pagebreak()

= Unicode

// https://tonsky.me/blog/unicode/
// https://www.joelonsoftware.com/2003/10/08/the-absolute-minimum-every-software-developer-absolutely-positively-must-know-about-unicode-and-character-sets-no-excuses

Sistemas de codificação são padrões criados para transformar caracteres em números, como `A`=$65$, `Ã`=$195$, `語`=$35486$ e 🤪=$129322$, e posteriormente serializá-los em mensagens para enviá-los a outras pessoas. O padrão Unicode é o sistema de representação de caracteres mais utilizado mundialmente hoje em dia, por incluir todas as linguagens existentes de maneira integrada. O padrão define 3 esquemas de codificação distintos para transformar caracteres Unicode em sequências de bits, UTF-8, UTF-16 e UTF-32, sendo UTF-8 de longe formato mais utilizado. Para entender o design e funcionamento desses, faz-se necessário entender como funcionavam os antecessores.

#quote(block: true, [Definição: _*code point*_ (ou *valor escalar*) é o nome dado à representação numérica de um caractere. No formato Unicode, é comum representá-los no formato `U+ABCDEF`, onde `ABCDEF` armazena o número do _code point_ em hexadecimal. ])

#quote(block: true, [Definição: um *codificador* é um programa que recebe valores escalares e transforma-os sequências de bits, e um *decodificador* é um programa que le sequências de bits e transforma-os de volta em valores escalares. ])

Sem dúvidas o sistema de codificação mais influente da história é o ASCII. Criado para servir as necessidades da indústria americana de _teleprinters_, o ASCII define apenas 127 caracteres, focando principalmente em compactar a quantidade de bits necessários para enviar uma mensagem, de forma que todo caracter pode ser expresso utilizando apenas 7 bits.

Com a evolução dos computadores, e a consolidação de um byte como 8 bits, muitos sistemas de codificação surgiram mantendo os primeiros 127 caracteres iguais a ASCII, e adicionando 128 caracteres no final, utilizando o oitavo bit previamente ignorado. Esses foram criados primariamente para adicionar suporte à caracteres especificos de cada linguagem, como `Ã`, `ç`, e `€`, de modo a manter compatibilidade com o ASCII, e ficaram conhecidos como codificações de ASCII estendido.

Tanto o ASCII quanto suas extensões utilizam um mapeamento um pra um entre o número dos caracteres e os bits das suas representações, tanto por simplicidade de codificação quanto por eficiência de armazenamento de memória. Programas que decodificam bytes em caracteres nesses sistemas são extremamente simples, e podem ser resumidos a tabelas de conversão direta, conhecidas como _code pages_.

Apesar da simplicidade dos programas, representar um byte por caractere coloca uma severa limitação no número de caracteres que conseguem expressar ($<= 256$), fazendo com que cada linguagem diferente tivesse sua própria maneira distinta de representar seus caracteres, e que muitas vezes era incompatível com as outras. Assim, enviar textos pela internet era uma tarefa complicada, visto que não era garantido que o usuário que recebe a mensagem teria as tabelas necessárias para decodificá-la corretamente.

Para piorar a situação, linguagens baseadas em ideogramas, como japonês, coreano e chinês, possuem milhares de caracteres, e codificá-las em apenas um byte é impossível. Tais linguagens foram pioneiras em encodings multi-bytes, em que um caractere é transformado em mais de um byte, tornando a codificação e decodificação significativamente mais complexa.

O padrão Unicode fora criado então para que um único sistema de codificação pudesse cobrir todas as linguagens, com todos seus caracteres específicos, de forma que qualquer texto escrito em qualquer linguagem pudesse ser escrito nele. Apesar de ambicioso, esse sistema rapidamente ganhou adoção massiva, estabelecendo sua posição como principal método de codificação da internet.

== UCS-2 e UTF-16

#let r(t) = text(fill: red, t)
#let g(t) = text(fill: green, t)
#let b(t) = text(fill: blue, t)
#let o(t) = text(fill: orange, t)
#let p(t) = text(fill: purple, t)
#let m(t) = text(fill: maroon, t)

Em 1991, a versão 1.0 do Unicode fora lançado pelo consórcio Unicode, com uma codificação de tamanho fixo de 16 bits conhecida por UCS-2 -- _Universal Coding System_ -- capaz de representar 65536 caracteres das mais diversas línguas. Rapidamente, esse sistema ganhou adoção em sistemas de grande relevância, como o sistema de UI Qt (1992), Windows NT 3.1 (1993) e até mesmo linguagens como Java (1995).

Tal quantidade, apesar de muito maior do que os antigos 256, rapidamente provou-se não suficiente para todas as linguagens. Quando isso fora percebido, o sistema UCS-2 já estava em amplo uso, e trocá-lo por outro sistema já não era mais uma tarefa trivial. Assim, para estendê-lo mantendo-o retro compatível, decidiram reservar parte da tabela de caracteres para que dois caracteres distintos (32 bits) representem um único _code point_. Dessa forma, o sistema deixou de ter um tamanho fixo de 16 bits, e passou a ter um tamanho variável, dependendo de quais _code points_ são codificados.

// https://en.wikipedia.org/wiki/UTF-16
O padrão UCS-2 estendido com _surrogate pairs_ tornou-se oficialmente o padrão UTF-16 na versão 2.0 do Unicode. Desde então, o uso do UCS-2 é desencorajado, visto que UTF-16 é considerado uma extensão em todos os aspectos a ele. Hoje em dia, na versão 17.0 do padrão Unicode, 297,334 _code points_ já foram definidos, muito além da projeção inicial de 65536.

Para determinar se uma sequência de bytes é válida em UTF-16, faz se necessário determinar se o primeiro byte representa o início de um _surrogate pair_, representado por bytes entre `D800` e `DBFF`, seguido de bytes que representam o fim de um _surrogate pair_, entre `DC00` e `DFFF`. Considerando a tabela 3.5 oferecida no capítulo 3.9 da especificação Unicode, o esquema de serialização pode ser visto da seguinte forma:
#let gr(t) = text(fill: gray, t)
#figure(
    align(center, table(columns: (auto, auto, auto, auto),
        align: (right, right, right, right),
        stroke: none,
        table.header("Valor escalar", table.cell(align:center, "Bytes"), table.cell(colspan: 2, align:center, "Inicio..Fim")),
        r(`xxxxxxxxxxxxxxxx`),  [#r(`xxxxxxxx`) #r(`xxxxxxxx`)], `U+0000`, `U+FFFF`,
        [#gr(`000`)#b(`uuuuu`)#r(`xxxxxxxxxxxxxxxx`)], [`110110`#g(`ww`) #g(`ww`)#r(`xxxxxx`) `110111`#r(`xx`) #r(`xxxxxxxx`)], `U+10000`, `U+10FFFF`,
    )), caption: [Distribuição dos bits em bytes válidos UTF-16. Nota: #g(`wwww`)` = `#b(`uuuuu`)` - 1`])

Assim, para que a decodificação de UTF-16 seja não ambígua, é necessário que _code points_ do primeiro intervalo, que não possuem cabeçalho para diferenciá-los, não possam começar com a sequência de bits `11011`. Além disso, iniciar um _surrogate pair_ (`D800..DBFF`) e não terminá-lo com um _code point_ no intervalo correto (`DC00..DFFF`) é considerado um erro, e é inválido segundo a especificação. De fato, o padrão Unicode explicita que *nenhum* _code point_ pode ser representado pelo intervalo `U+D800..U+DFFF`, de forma que os outros sistemas de codificação -- UTF-8, UTF-32 -- tenham que desenvolver sistemas para evitar que esses sejam considerados _code points_ válidos.

A quantidade de _code points_ definidos pelo Unicode está diretamente ligada à essas limitações do padrão UTF-16, que consegue expressar $1.112.064$ _code points_. Esse número pode ser calculado da seguinte forma:
#figure(align(center, table(columns: (auto, auto, auto),
    stroke: none,
    table.header("Inicio..Fim", "Tamanho", "Descrição"),
    `U+0000..U+FFFF`, $2^16$, "Basic Multilingual Plane, Plane 0",
    `U+D800..U+DFFF`, $2^11$, "Surrogate Pairs",
    `U+10000..U+10FFFF`, $2^20$, "Higher Planes, Planes 1-16",
    table.hline(), 
    [`U+0000..U+10FFFF` #sym.without `U+D800..U+DFFF`], $2^20 + 2^16 - 2^11$, [_Code points_ representáveis]
)), caption: [Intervalos de _code points_ válidos.])

Disso, pode-se inferir que um _code point_ *válido* é um número de 21 bits que:
1. Não está no intervalo `U+D800..U+DFFF`.
2. Não ultrapassa `U+10FFFF`.

// https://nvd.nist.gov/vuln/detail/CVE-2008-2938
// https://nvd.nist.gov/vuln/detail/CVE-2012-2135

É importante ressaltar que há ambiguidade na forma de serializar UTF-16 para bytes, visto que não é especificado pelo Unicode se o primeiro byte de um _code point_ deve ser o mais significativo -- Big Endian -- ou o menos significativo -- Little Endian. Para distinguir, é comum o uso do caractere `U+FEFF`, conhecido como _Byte Order Mark_ (BOM), como o primeiro caractere de uma mensagem ou arquivo. No caso de Big Endian, o BOM aparece como `FEFF`, e no caso de Little Endian, aparece como `FFFE`.

Essa distinção faz com que UTF-16 seja divido em duas sub linguagens, UTF-16BE (Big Endian) e UTF-16LE (Little Endian), adicionando ainda mais complexidade à tarefa de codificar e decodificar os caracteres corretamente.

Com essas complexidades, implementar codificação e decodificação de UTF-16 corretamente tornou-se muito mais complicado. Determinar se uma sequência de bytes deixou de ser uma tarefa trivial, e tornou-se um possível lugar onde erros de segurança podem acontecer. De fato, CVE-2008-2938 e CVE-2012-2135 são exemplos de vulnerabilidades encontradas em funções relacionadas à decodificação em UTF-16, em projetos grandes e bem estabelecidas (APACHE e Python, respectivamente).

Apesar de extremamente útil, o UTF-16 utiliza 2 bytes para cada caractere, então não é eficiente para linguagens cujos caracteres encontram-se no intervalo original do ASCII (1 byte por caractere). Em especial formatos comumente utilizados na internet, como HTML e JSON, usam muitos caracteres de pontuação -- `<`, `>`, `{`, `:` -- contidos no intervalo do ASCII. Por isso, fez-se necessário achar outra forma de codificá-los que fosse mais eficiente para a comunicação digital.

== UTF-8

Criado por Rob Pike e Ken Thompson, o UTF-8 surgiu como uma alternativa ao UTF-16 que utiliza menos bytes. A principal mudança para que isso fosse possível foi a de abandonar a ideia de codificação de tamanho fixo desde o início, dificultando ainda mais a implementação de decodificadores corretos, e preferindo uma codificação de tamanho variável.

A quantidade de bytes necessários para representar um _code point_ em UTF-8 é uma função do intervalo que esse _code point_ se encontra. Ao invés de serializar os _code points_ diretamente, como o UTF-16 fazia, agora todos os bytes contém cabeçalhos, que indicam o tamanho da serialização do _code point_ -- isto é, a quantidade de bytes a seguir.

Para _code points_ no intervalo `U+0000..U+007F`, apenas 1 byte é usado, e esse deve começar com o bit `0`. Para _code points_ no intervalo `U+0080..07FF`, dois bytes são usados, o primeiro começando com os bits `110`, e o segundo sendo um byte de continuação, que contém o cabeçalho `10`. Para aqueles no intervalo `U+0800..U+FFFF`, o primeiro byte deve começar com `1110`, seguido de dois bytes de continuação, e por fim, aqueles no intervalo `U+10000..U+10FFFF`, o primeiro byte deve começar com `11110`, seguido de três bytes de continuação.

Considerando a tabela 3.6 do capítulo 3.9 da especificação, podemos representar como os bytes serializados com a seguinte tabela:
#figure(align(center, table(columns: (auto, auto, auto, auto, auto, auto, auto),
    align: (right, right, right, right, right, right, left),
    stroke: none,
    table.header(table.cell(align:center, "Bits do Valor Escalar"), table.cell(colspan:4, align:center, "Bytes"), table.cell(colspan: 2, align:center, "Início..Fim")),
    [#gr(`00000`) #gr(`00000000`) #gr(`0`)#r(`xxxxxxx`)], [], [], [], [`0`#r(`xxxxxxx`)], `U+0000`, `U+007F`,
    [#gr(`00000`) #gr(`00000`)#b(`yyy`) #b(`yy`)#r(`xxxxxx`)], [], [], [`110`#b(`yyyyy`)], [`10`#r(`xxxxxx`)], `U+0080`, `U+07FF`,
    [#gr(`00000`) #o(`zzzz`)#b(`yyyy`) #b(`yy`)#r(`xxxxxx`)], [], [`1110`#o(`zzzz`)], [`10`#b(`yyyyyy`)], [`10`#r(`xxxxxx`)], `U+0800`, `U+FFFF`,
    [#p(`uuuuu`) #o(`zzzz`)#b(`yyyy`) #b(`yy`)#r(`xxxxxx`)], [`11110`#p(`uuu`)], [`10`#p(`uu`)#o(`zzzz`)], [`10`#b(`yyyyyy`)], [`10`#r(`xxxxxx`)], `U+10000`, `U+10FFFF`,
)), caption: [Distribuição dos bits em bytes UTF-8.]) <UTF8_bits>

É importante notar que os primeiros 127 _code points_ são representados exatamente igual caracteres ASCII em apenas 1 byte, algo extremamente desejável não apenas para compatibilidade com sistemas antigos, mas para recuperar parte da eficiência de espaço perdida no UTF-16. Diferentemente do UTF-16, o UTF-8 também não possui ambiguidade de _endianness_, e portanto não precisa utilizar o BOM para desambiguar; há apenas uma maneira de ordenar os bytes.

O UTF-8 ainda precisa manter as limitações do UTF-16, visto que ambos codificam o mesmo conjunto de _code points_. Como _surrogate pairs_ não são mais utilizados para representar _code points_ estendidos, é necessário garantir que bytes do intervalo `D800..DFFF` nunca apareçam, já que não possuem significado.

Além disso, apesar de conseguir codificar 21 bits no caso com maior capacidade (`U+0000..U+1FFFFF`), nem todos desses representam _code points_ válidos, dado que o padrão Unicode define-os baseando nos limites do UTF-16. Isso significa que o codificador deve assegurar de que todos _code points_ decodificados não sejam maior do que `U+10FFFF`.

As primeiras versões da especificação do UTF-8 não faziam distinção de qual o tamanho deveria ser utilizado para codificar um _code point_. Por exemplo, o caractere `A` é representado por `U+0041 = `#r(`1000001`). Isso significa que ele podia ser representado em UTF-8 como qualquer uma das seguintes sequências:

#let gr(t) = text(fill: gray, t)
#figure(align(center, table(columns: (auto, auto),
    align: (right, left),
    stroke: none,
    table.header("Sequência de bits", "Hexadecimal"),
    [`0`#r(`1000001`)], `41`,
    [`110`#gr(`0000`)#r(`1`) `10`#r(`000001`)], `C1 81`,
    [`1110`#gr(`0000`) `10`#gr(`00000`)#r(`1`) `10`#r(`000001`)], `E0 81 81`,
    [`11110`#gr(`000`) `10`#gr(`000000`) `10`#gr(`00000`)#r(`1`) `10`#r(`000001`)], `F0 80 81 81`,
)), caption: [Possíveis representações para o caracter `U+0041`.])

// https://www.cve.org/CVERecord?id=CVE-2010-3870
// https://kevinboone.me/overlong.html

Permitir tais codificações causou inúmeras vulnerabilidades de segurança, visto que vários programas erroneamente ignoram a noção de _code points_ e tratam esses como sequências de bytes diretamente. Ao tentar proibir certos caracteres de aparecerem em uma string, os programas procuravam por sequências de bytes especificamente, ao invés de _code points_, e ignoravam que um _code point_ podia ser codificado de outra forma. As CVEs CVE-2008-2938 e CVE-2000-0884 estão associadas diretamente com má filtragem de caracteres em strings, permitindo que o atacante codifique caracteres proibidos com diferentes sequências de bytes (`/`, `..`) e ultrapasse todas as checagens.

O padrão Unicode nomeou esses casos como _overlong encodings_, e modificou especificações futuras para que a única codificação válida de um _code point_ em UTF-8 seja a menor possível. Isso adiciona ainda mais dificuldade na hora de decodificar os bytes, visto que o conteúdo do _code point_ deve ser observado, para checar se fora codificado do tamanho certo.

Assim, validar que uma sequência de bytes representa UTF-8 válido significa respeitar as seguintes propriedades:
1. Nenhum byte está no intervalo de _code points_ de _surrogate pairs_ (`U+D800..U+DFFF`), e consequentemente, nenhum _code point_ deve ocupar esse intervalo também.
2. Todo _code point_ lido é menor ou igual a `U+10FFFF`
3. Todo _code point_ é escrito na menor quantidade de bytes necessária para expressá-lo, isto é, não há _overlong encoding_.
4. Todo byte de início começa com o header correto (a depender do intervalo do _codepoint_).
5. Todo byte de continuação começa com o header correto (`10`).

== Revisão de literatura

// https://www.swift.org/blog/utf8-string/
// https://github.com/rust-lang/rust/blob/master/library/core/src/str/validations.rs#L126
// TODO: figure out whatever the hack swift does for UTF-8 validation:
// https://github.com/swiftlang/swift/blob/89b43dccf31d5331cd7fe1336d44e6407e08eadc/stdlib/public/core/UTF8.swift#L14

A proposição original do sistema de codificação UTF-8 fora dada no RFC3629, que passou por múltiplas revisões, até ser oficialmente transferida para a especificação Unicode, a partir de sua versão 4.0, em 2003. Desde então, a definição autoritária para esse esquema é dada pelo Consórcio Unicode, dentro da especificação geral do sistema Unicode.

No capítulo 3.9 da especificação do sistema Unicode, são definidos conceitos gerais de codificação, bem como os formatos UTF-8, UTF-16 e UTF-32. Nesse capítulo, duas definições importantes são feitas:

1. [D77] *Valor escalar*: um valor escalar Unicode é qualquer code point que não está no intervalo de _surrogate pairs_. (Esse definição é a mesma de code points válidos dada anteriormente.)
2. [D79] *Esquema de codificação Unicode*: um mapeamento único entre um valor escalar e uma sequência de bytes. A especificação oferece a definição de três esquemas de codificação oficiais: UTF-32 ([D90]), UTF-16 ([D91]) e UTF-8 ([D92]). 

Segundo a definição D92, o UTF-8 é um formato de codificação que transforma um escalar Unicode em uma sequência de 1 a 4 bytes, cujos bits representam code points exatamente como especifiado na @UTF8_bits. Para decidir quais bytes são UTF-8 válidos, é oferecida a tabela 3.7, reproduzida abaixo em verbatim:

#figure(align(center, table(columns: (auto, auto, auto, auto, auto, auto),
    align: (right, right, left, right, right, right),
    stroke: none,
    table.header(table.cell(colspan: 2, align:center, "Início..Fim"), table.cell(align:center, "Byte 1"), table.cell(align:center, "Byte 2"), table.cell(align:center, "Byte 3"), table.cell(align:center, "Byte 4")),
    table.hline(),
    [`U+0000`], [`U+007F`], [`00..7F`],       none, none, none,
    table.hline(stroke: (thickness: 0.5pt, dash:"dashed")),
    [`U+0080`], [`U+07FF`], [`C2..DF`], [`80..BF`], none, none,
    table.hline(stroke: (thickness: 0.5pt, dash:"dashed")),
    [`U+0800`], [`U+0FFF`], [`E0`], [*`A0`*`..BF`], [`80..BF`], none,
    [`U+1000`], [`U+CFFF`], [`E1..EC`], [`80..BF`], [`80..BF`], none,
    [`U+D000`], [`U+D7FF`], [`ED`], [`80..`*`9F`*], [`80..BF`], none,
    [`U+E000`], [`U+FFFF`], [`EE..EF`], [`80..BF`], [`80..BF`], none,
    table.hline(stroke: (thickness: 0.5pt, dash:"dashed")),
    [`U+10000`], [`U+3FFFF`], [`F0`], [*`90`*`..BF`], [`80..BF`], [`80..BF`],
    [`U+40000`], [`U+FFFFF`], [`F1..F3`], [`80..BF`], [`80..BF`], [`80..BF`],
    [`U+100000`], [`U+10FFFF`], [`F4`], [`80..`*`8F`*], [`80..BF`], [`80..BF`],
)), caption: [Sequências de bytes UTF-8 bem formadas.]) <UTF8_bytes>

Os intervalos `80..BF` representam os intervalos comuns de continuação -- isto é, bytes que começam com `10` sempre estão nesse intervalo -- e portanto, os bytes que diferem desses estão marcados em negrito. Essas diferenças são necessárias para evitar os casos de _overlong encoding_ -- onde o _code point_ representado caberia em uma representação menor -- e de _surrogate pair_ -- onde o _code point_ representado estaria no intervalo `D800..DFFF`.

No caso em que o _code point_ está no intervalo ASCII, ele é representado sem restrições. Quando é necessário dois bytes, o primeiro não pode começar com `C0` ou `C1` pois faria o _code point_ resultante caber no intervalo anterior. No caso de 3 bytes, há a possibilidade de o _code point_ equivalente estar no intervalo `D800..DFFF`, e por isso é separado em 4 intervalos distintos. O primeiro intervalo se preocupa em impedir que ocorra _overlong encoding_, restringindo o segundo byte; o segundo intervalo contém apenas bytes estritamente menores do que `U+D000`; o terceiro intervalo restringe o segundo byte para garantir que seja menor do que `U+D7FF`; o último intervalo representa aqueles estritamente maiores do que `U+DFFF`. Da mesma forma, o caso de 4 bytes é separado em três. O primeiro caso se preocupa em impedir _overlong encoding_, enquanto o último caso garante que o _code point_ seja estritamente menor do que `U+10FFFF` (o maior _code point_ válido).

Nessa especificação, não fica clara a relação entre a tabela descritiva e as propriedades intrínsecas ao UTF-8. Não é óbvio que há uma correspondência única entre sequências de bytes e _code points_ válidos, nem que todo _code point_ representado pela @UTF8_bytes é necessariamente válido. Além disso, as operações de extração e concatenação de bits, que são oferecidas implicitamente pela @UTF8_bits, não são triviais, e são sucetíveis a erros. Com uma especificação complicada demais, é possível que erros sejam cometidos até mesmo na concepção das regras. Assim, quanto menor o conjunto de regras, mais fácil é de conferir manualmente que elas estão corretas.

== Trabalhos relacionados

Faz-se necessário, portanto, estudar como codificadores e decodificadores são especificados e formalizados tradicionalmente. Em geral, para mostrar a *corretude funcional* de ambos, é interessante mostrar que o codificador e decodificador recuperam os valores de entrada originais um do outro. Isto é, a grosso modo, mostrar que `encoder a = b` se, e somente, `decoder b = a`.

@Ye2019 descrevem o processo de implementar em Rocq um gerador de codificador e decodificador para Protobuf. Como o protocolo permite que o usuário gere formatos binários baseado em arquivos de configuração, os autores oferecem uma formalização da semântica para os arquivos _protocol buffers_, e utilizam-a para gerar programas que codificam e decodicam os formatos específicados em um arquivo, junto das provas de que os programas gerados devem obedecer a essa semântica corretamente e que esses necessariamente são inversos um do outro.

@Koprowski2010 forneceram uma implementação similar para linguagens que podem ser descritas por PEGs em Rocq, junto de exemplos práticos de implementações de parsers de XML e da linguagem Java. @vanGeest2017 desenvolveram uma biblioteca em Agda para descrever pacotes em formários abitrários, focando no caso de uso dos padrões ASN.1, fornecendo uma formalização de formato IPV4. Ambos utilizam a noção de inversibilidade entre o codificador e decodificador como fundamento para a corretude.

@thery2004 formalizou uma implementação do algoritmo de Huffman, frequentemente utilizado em padrões de compressão sem perda de dados. Similarmente @DeflateInCoq2016 construiram uma implementação completa do algoritmo de Deflate, usado em formatos como PNG e GZIP. Para mostrar a corretude, ambos provam a corretude mostrando que o codificador e decodificador são inversos.

@Delaware2019 desenvolveram uma biblioteca em Rocq, _Narcissus_, que permite o usuário de descrever formatos binários de mensagens em uma DSL dentro do provador interativo. A principal contribuição do artigo é utilizar o maquinário nativo de Rocq para derivar tanto as implementações e as provas utilizando macros de forma que o sistema seja extremamente expressivo. Em casos que a biblioteca não é forte o suficiente para gerar as provas, o usuário é capaz de fornecer provas manualmente escritas para a corretude, de forma a estender as capacidades do sistema.

@PulseParse2025 desenvolveram uma biblioteca parecida chamada _PulseParse_ na linguagem F\*, para implementar serializadores e desserializadores para vários formatos: CBOR, um formato binário inspirado em JSON, e CDDL, uma linguagem que especifica formatos estáticos CBOR. Utilizando essa biblioteca, os autores fornecem uma semântica ao CDDL e provam a corretude de programas gerados em cima desse conforme essa semântica.

Para a simplicidade de implementação, a formalização dada neste trabalho não utilizará nenhuma biblioteca, visto que essas introduzem complexidades especificas de cada DSL. Assim, quase tudo será feito do zero.

#pagebreak()

= Formalização da especificação

Visto que a especificação fornecida pelo Consórcio Unicode não é formal o suficiente, tornou-se necessário estabelecer precisamente quais as propriedades que o codificador e decodificador devem satisfazer pra que sejam considerados corretos. Como visto nos outros trabalhos, é interessante conseguir provar que quaisquer codificador e decodificador que respeitam a especificação devem necessariamente ser inversos um do outro.

Para garantir a corretude da especificação, é importante se preocupar com como representar sequências de _code points_ e sequências de bytes, de forma que seja possível aplicar o mapa anterior repetidamente, acumulando seu resultado. Para representar ambos será utilizado o tipo `Z`, que representa o conjunto dos inteiros em Rocq, pois ele possui uma grande gama de propriedades úteis já provadas previamente, de modo que muitas relações matemáticas possam ser reutilizadas. Para representar sequências desses, em linguagens funcionais é tradicional representar strings como listas encadeadas, de forma que tanto as sequências de bytes quanto sequências de codepoints sejam representados como listas encadeadas de inteiros:

```coq
Definition codepoint : Type := Z.
Definition byte : Type := Z.

Definition unicode_str : Type := list codepoint.
Definition byte_str : Type := list byte.
```

Assim, faz sentido considerar que ambos o codificador e o decodificador sejam funções que mapeiam uma lista de números em uma nova lista de números, mas isso não leva em consideração que ambas podem receber argumentos inválidos. De fato, é necessária uma maneira de sinalizar que a lista retornada não era uma sequência UTF-8 válida.

Para formalizar codificadores e decodificadores, será utilizada a noção de _parser_. De modo geral, _parsers_ processam elementos de tipo `A` e retornam algum valor de tipo `B`, e são utilizados quando a transformação pode não funcionar em todos os casos. Assim, é tradicional utilizar alguma estrutura que envolve o resultado `B` em múltiplos casos para representar a falibilidade.

O exemplo mais comum dessa estrutura é `option B`, que pode ser tanto `Some` com um valor de tipo `B`, ou `None`, representando que o `parser` falhou em extrair informação da entrada.
```coq
Inductive option (B :Type) : Type :=
  | Some : B -> option B
  | None : option B.
```

Entretanto, o problema de utilizar o tipo `option` é que é possível que uma sequência de bytes seja quase inteiramente UTF-8 válida, mas tenha algum erro por corrupção na hora da transmissão. Nesse caso, o `parser` retornaria `None`, e toda informação seria descartada. Ao invés disso, é útil exigir que o `parser` tente sempre ler o maior número de bytes o possível do prefixo da entrada, e ao encontrar bytes inválidos, substitua-os pelo caractere '#str.from-unicode(65533)' (`U+FFFD`). Essa prática é tão difundida que o capítulo 3.9.6 do padrão Unicode dá guias gerais sobre como essa substituição deve ser feita.

É possível especificar o algoritmo de substituição como um _parser_ que roda o decodificador UTF-8 e substitui as partes inválidas de acordo com o que especificado no capítulo 3.9.6. Entretanto, este trabalho é restringido à leitura do prefixo válido na entrada, e o decodificador que aplica as substituições pode ser feito como extensão em um trabalho futuro.

Assim, um _parser_ parcial é definido como uma função que recebe uma lista de elementos de tipo `input` e retorna um par de `output` e lista de `input`. A semântica de um _parser_ parcial é de que a lista de `output` representa o resultado de "consumir" o prefixo válido da lista de entrada, enquanto a lista de `input` no resultado representa o sufixo não consumido. Essa semântica é enforçada como propriedades na especificação, vistas mais a frente.

```coq
Definition partial_parser (input output: Type) := list input -> (output * list input).

Definition encoder_type := partial_parser codepoint (list byte).
Definition decoder_type := partial_parser byte (list codepoint).
```

Para especificar unicamente o mapeamento entre sequências de bytes e codepoints, devem ser utilizadas as tabelas @UTF8_bits e @UTF8_bytes. Uma possível maneira de traduzir isso em código Rocq seria com uma propriedade entre uma lista de inteiros e um inteiro, que faz a tradução direta:
```coq
Inductive naive_utf8_map : byte_str -> codepoint -> Prop :=
| OneByte (b1: byte) :
  0x00 <= b1 < 0x80 ->
  naive_utf8_map [b1] b1
| TwoBytes (b1 b2: byte) :
  0xc2 <= b1 <= 0xdf ->
  0x80 <= b2 <= 0xbf ->
  naive_utf8_map [b1; b2] ((b1 mod 64) * 64 + (b2 mod 64))
| ThreeBytes1 (b1 b2 b3: Z):
  b1 = 0xe0 ->
  0xa0 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  naive_utf8_map [b1; b2; b3] (((b1 - 224) * 4096) + (b2 mod 64) * 64 + (b3 mod 64))
| ThreeBytes2 (b1 b2 b3: Z):
  0xe1 <= b1 <= 0xec \/ 0xee <= b1 <= 0xef ->
  0x80 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  naive_utf8_map [b1; b2; b3] (((b1 - 224) * 4096) + (b2 mod 64) * 64 + (b3 mod 64))
| ThreeBytes3 (b1 b2 b3: Z):
  b1 = 0xed ->
  0x80 <= b2 <= 0x9f ->
  0x80 <= b3 <= 0xbf ->
  naive_utf8_map [b1; b2; b3] (((b1 - 224) * 4096) + (b2 mod 64) * 64 + (b3 mod 64))
| FourBytes1 (b1 b2 b3 b4: Z):
  b1 = 0xf0 ->
  0x90 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  naive_utf8_map [b1; b2; b3; b4] ((b1 - 240) * 262144 + (b2 mod 64) * 4096 + (b3 mod 64) * 64 + (b4 mod 64))
| FourBytes2 (b1 b2 b3 b4: Z):
  0xf1 <= b1 <= 0xf3 ->
  0x80 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  naive_utf8_map [b1; b2; b3; b4] ((b1 - 240) * 262144 + (b2 mod 64) * 4096 + (b3 mod 64) * 64 + (b4 mod 64))
| FourBytes3 (b1 b2 b3 b4: Z):
  b1 = 0xf4 ->
  0x80 <= b2 <= 0x8f ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  naive_utf8_map [b1; b2; b3; b4] ((b1 - 240) * 262144 + (b2 mod 64) * 4096 + (b3 mod 64) * 64 + (b4 mod 64)).
```

Isto é, um elemento de tipo `naive_utf8_map bytes codepoint` é uma prova de que a sequência de bytes `bytes` mapeia para o codepoint `codepoint` segundo as tabelas @UTF8_bits e @UTF8_bytes. Especificamente, cada construtor de `naive_utf8_map` representa uma das linhas da @UTF8_bytes, e as operações nos bytes de multiplicação e `mod` representam como extrair os bits relevantes dos bytes que contém cabeçalhos.

O problema de incluir as operações de bits na especificação é que não há como afirmar com certeza que essas operações representam exatamente o que é dado na @UTF8_bits, visto que as operações de bit shift foram desenvolvidas manualmente. Parte crucial de verificação de software é que a especificação seja simples de entender, para que seja checável manualmente por um ser humano, e escrever as operações nos bits diretamente é um processo que facilmente induz a erros.

Para especificar exatamente qual o mapeamento dado entre bytes e codepoints, é mais interessante considerar propriedades que esse deve satisfazer. Especificamente, é simples explicitar as propriedades que ditam o que é uma sequência de bytes UTF-8 válidas (@UTF8_bytes) e o que é um _code point_ válido, exigindo que o codificador mapeie _code points_ válidos em bytes UTF-8 válidos, e o decodificador mapeie bytes UTF-8 válidos em _code points_ válidos. Entretanto, existem inúmeras maneiras de fazer esse mapeamento de modo que o codificador e decodificador sejam inversos, e apenas um desses de fato é o UTF-8.

Assim, uma propriedade muito simples sobre o mapeamento de _code points_ em bytes é denotada no RFC 3629:
// https://datatracker.ietf.org/doc/html/rfc3629
#quote(block: true, [
    "A ordenação lexicográfica por valor dos bytes de strings UTF-8 é a mesma que se fosse ordenada pelos números dos caracteres. É claro, isso é de interesse limitado, dado que uma ordenação baseada no número dos caracteres quase nunca é culturalmente válida." (@rfc3629)
])

Apesar do que foi dito pelo autor do RFC, essa propriedade é de extremo interesse para a formalização por sua simplicidade de enunciação. Para garantir que _code points_ sejam mapeados nas respectivas representações de bytes, basta exigir que tanto o codificador quanto o decodificador respeitem a ordenação lexicográfica entre _code points_ e bytes.

Essa propriedade pode ser facilmente compreendida dado dois argumentos informais: os intervalos de  _code points_ representados por sequências de bytes de tamanhos diferentes são disjuntos, ou seja, e os cabeçalhos no início do byte são suficiente para determinar que uma sequência de tamanho distinto é menor ou maior. Isto é, um _code point_ no primeiro intervalo serializa como `b1 ~ 0xxxxxxx`, e sempre será menor que um no segundo intervalo, que serializa como `b2 ~ 110xxxxx`, o que implica que `b1 < b2`, dado que `b1 <= 0x7F` e `0xC0 <= b2`. O mesmo é válido para todas as outras comparações entre sequências de bytes de tamanhos distintos.

Assim, _code points_ de intervalos distintos devem necessariamente serializar para bytes ordenados lexicograficamente, visto que o primeiro byte é suficiente para determinar qual é maior. Basta agora mostrar que _code points_ de um mesmo intervalo devem serializar ordenadamente. Mas isso é trivial, visto todos os bytes das duas sequências devem ter cabeçalhos idênticos, e os bits do _code point_ são serializados ordenadamente, fazendo com que comparar lexicograficamente as sequências de bytes seja equivalente a comparar os bits dos _code points_ originais. 

Ou seja, é possível caracterizar unicamente codificadores e decodificadores de UTF-8 como funções que mapeiam bytes no formato da @UTF8_bytes em _code points_ válidos (e vice versa), *que respeitam a ordenação entre _code points_ e bytes*. Essa é a principal ideia por trás da especificação deste trabalho, e o objetivo da formalização é mostrar que apenas essas propriedades são suficientes para provar que quaisquer par de codificador e decodificador que respeitam-a devem ser inversos.

Uma vantagem prática de utilizar a comparação para identificar o mapeamento na especificação, ao invés das operações em bits, é que não é necessário mostrar que o _code point_ tem o mesmo valor exato. É possível que uma implementação utilize operações distintas e chegue no mesmo resultado correto. Por exemplo, é razoável imaginar que um usuário deseje implementar operações específicas de bit _shifts_ e _masks_ que não utilizam multiplicação e `mod`, e torna-se parte da prova mostrar que as operações devem ser iguais numericamente. Utilizar a comparação oferece mais flexibilidade ao usuário que prova a especificação, pois tudo que é necessário é dizer que a operação escolhida é crescente.

Tendo isso em mente, definimos as seguintes notações:
```coq
Definition codepoint : Type := Z.
Definition byte : Type := Z.

Definition unicode_str : Type := list codepoint.
Definition byte_str : Type := list byte.
Definition codepoints_compare := List.list_compare Z.compare.
Definition bytes_compare := List.list_compare Z.compare.
```

As funções `codepoints_compare` e `bytes_compare` são utilizadas exatamente para prover as comparações entre inteiros. A função `Z.compare` é oferecida pela biblioteca padrão do Rocq, recebendo dois inteiros e retorna o resultado da comparação entre eles, do tipo `comparison`:
```coq
Inductive comparison : Set :=
  | Eq : comparison
  | Lt : comparison
  | Gt : comparison.
```

A função `list_compare` transforma uma comparação entre elementos de um tipo `T` em uma comparação entre elementos de tipo `list T`, utilizando a semântica de comparação lexicográfica. Inúmeras propriedades sobre as funções de comparação `Z.compare` e `list_compare` já são oferecidas por padrão, como antissimetria, transitividade e reflexividade. De fato, veremos mais a frente que essas propriedades são chave para provar o teorema sobre a unicidade do mapeamento.

Em seguida, definimos as propriedades necessárias para afirmar que um `codepoint` arbitrário, isto é, um inteiro qualquer, é um _code point_ UTF-8 válido. Como visto anteriormente, basta saber que esse está entre `0x0` e `0x10FFFF`, e não está no intervalo `0xD800..0xDFFF` . Isso pode ser representado como as seguintes três propriedades:
```coq
Definition codepoint_less_than_10ffff (code: codepoint) : Prop :=
  (code <= 0x10ffff).

Definition codepoint_is_not_surrogate (code: codepoint) : Prop :=
  (code < 0xd800) \/ (code > 0xdfff).

Definition codepoint_not_negative (code: codepoint): Prop :=
  (code >= 0).

Definition valid_codepoint (code: codepoint) := codepoint_less_than_10ffff code /\ codepoint_is_not_surrogate code /\ codepoint_not_negative code.
```

Isto é, provar que `valid_codepoint code` para algum `code` significa mostrar que as três propriedades valem ao mesmo tempo.

Para definir o tipo `valid_codepoint_representation`, será utilizada a mesma ideia do `naive_utf8_map`. Isto é, esse só pode ser construido quando os elementos da lista de entrada estão nos intervalos de alguma das linhas da tabela, e representa afirmar que uma certa lista de bytes é a representação em UTF-8 de *algum* _code point_. Diferentemente do `naive_utf8_map`, não é dado o valor do _code point_ específico que essa sequência mapeia, e apenas se afirma que essa é válida segundo @UTF8_bytes.

```coq
Inductive valid_codepoint_representation : list Z -> Prop :=
| OneByte (b: Z) :
  0 <= b <= 0x7f ->
  valid_codepoint_representation [b]
| TwoByte (b1 b2: Z):
  0xc2 <= b1 <= 0xdf ->
  0x80 <= b2 <= 0xbf ->
  valid_codepoint_representation [b1; b2]
| ThreeByte1 (b1 b2 b3: Z):
  b1 = 0xe0 ->
  0xa0 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3]
| ThreeByte2 (b1 b2 b3: Z):
  0xe1 <= b1 <= 0xec \/ 0xee <= b1 <= 0xef ->
  0x80 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3]
| ThreeByte3 (b1 b2 b3: Z):
  b1 = 0xed ->
  0x80 <= b2 <= 0x9f ->
  0x80 <= b3 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3]
| FourBytes1 (b1 b2 b3 b4: Z):
  b1 = 0xf0 ->
  0x90 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3; b4]
| FourBytes2 (b1 b2 b3 b4: Z):
  0xf1 <= b1 <= 0xf3 ->
  0x80 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3; b4]
| FourBytes3 (b1 b2 b3 b4: Z):
  b1 = 0xf4 ->
  0x80 <= b2 <= 0x8f ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3; b4].
```

Com isso, existem duas maneiras de construir uma lista de bytes válidos UTF-8: ou a lista é vazia, ou ela é a concatenação de uma representação em bytes de um `codepoint` e uma lista de bytes UTF-8 válidos. O tipo que representa que essa relação é:
```coq
Inductive valid_utf8_bytes: list Z ->  Prop :=
| Utf8Nil : valid_utf8_bytes []
| Utf8Concat (bytes tail: list Z) :
    valid_codepoint_representation bytes ->
    valid_utf8_bytes tail ->
    valid_utf8_bytes (bytes ++ tail).
```

Apenas essas definições são suficientes para começar a definir as propriedades que o codificador e decodificador devem seguir:
```coq
Definition encoder_nil (encoder: encoder_type) := encoder [] = ([], []).
```
A primeira propriedade dita que o `encoder` deve aceitar a lista vazia com o resultado vazio.

```coq
Definition encoder_input_correct_iff (encoder: encoder_type) := forall code,
    valid_codepoint code <->
    exists bytes, encoder [code] = (bytes, []).
```

A segunda propriedade é uma dupla implicação: da esquerda para direita, diz que o `encoder` deve aceitar todo `codepoint` válido; da direita para esquerda, diz que se o encoder aceita uma lista com um `codepoint` apenas, então esse `codepoint` é válido.

```coq
Definition encoder_output_correct (encoder: encoder_type) := forall code,
    match encoder [code] with
    | (bytes, []) => valid_codepoint_representation bytes
    | (bytes, rest) => bytes = [] /\ rest = [code]
    end.
```
A terceira propriedade descorre sobre a validade do resultado de um `encoder`. Apenas dois resultados ao chamar um `encoder` com uma lista de um elemento são possíveis: ou a entrada é aceita, e os `bytes` à esquerda são uma representação de codepoints válida, ou não é aceita, o que implica que os `bytes` devem ser vazios, e o lado não consumido deve conter o `codepoint` da entrada. 

```coq
Definition encoder_strictly_increasing (encoder: encoder_type) := forall code1 code2 bytes1 bytes2,
    encoder [code1] = (bytes1, nil) ->
    encoder [code2] = (bytes2, nil) ->
    Z.compare code1 code2 = bytes_compare bytes1 bytes2.
```

A quarta propriedade afirma que o `encoder` respeita a ordenação lexicográfica entre bytes e _code points_, explicada anteriormente. Essa propriedade é suficiente para afirmar que o `encoder` mapeia o _code point_ na sua respectiva representação em bytes, de acordo com o mapeamento UTF-8.

```coq
Definition encoder_projects (encoder: encoder_type) := forall xs ys,
    encoder (xs ++ ys) =
      match encoder xs with
      | (bytes, nil) =>
          let (bytes2, rest) := encoder ys in
          (bytes ++ bytes2, rest)
      | (bytes, rest) => (bytes, rest ++ ys)
      end.
```

Por fim, a quinta e última propriedade é a que descreve como o `encoder` deve se comportar perante listas grandes. Quando uma lista pode ser quebrada em duas listas menores, o resultado de chamar o `encoder`  na lista maior é igual a chamar na primeira, e se for aceita, chamar na segunda e concatenar os resultados. No caso de erro, o encoder para imediatamente.

```coq
Record utf8_encoder_spec encoder := {
    enc_nil : encoder_nil encoder;
    enc_increasing : encoder_strictly_increasing encoder;
    enc_input : encoder_input_correct_iff encoder;
    enc_output : encoder_output_correct encoder;
    enc_projects : encoder_projects encoder;
  }.
```

Apenas essas 5 propriedades são o suficiente para qualificar um `encoder` como um codificador de UTF-8 válido, segundo a especificação. Importantemente, não é necessário ter um decodificador para provar que o codificador está correto. Para provar que um `encoder` está certo, basta construir um elemento de tipo `utf8_encoder_spec encoder`.

As propriedades que o decodificador deve satisfazer são análogas às do codificador.
```coq
Definition decoder_nil (decoder: decoder_type) := decoder nil = (nil, nil).

Definition decoder_output_correct (decoder: decoder_type) := forall bytes suffix codes,
    decoder bytes = (codes, suffix) ->
    valid_codepoints codes /\
      (exists prefix,
          decoder prefix = (codes, [])
          /\ valid_utf8_bytes prefix
          /\ bytes = prefix ++ suffix).

Definition decoder_input_correct_iff (decoder: decoder_type) := forall bytes,
    valid_codepoint_representation bytes <->
    exists code, decoder bytes = ([code], []).

Definition decoder_strictly_increasing (decoder: decoder_type) := forall bytes1 bytes2 code1 code2,
    decoder bytes1 = ([code1], nil) ->
    decoder bytes2 = ([code2], nil) ->
    Z.compare code1 code2 = bytes_compare bytes1 bytes2.

Definition decoder_projects (decoder: decoder_type) := forall xs ys,
    valid_codepoint_representation xs ->
    decoder (xs ++ ys) =
      let (codes, _) := decoder xs in
      let (codes2, rest) := decoder ys in
      (codes ++ codes2, rest).

Record utf8_decoder_spec decoder := {
    dec_nil : decoder_nil decoder;
    dec_input : decoder_input_correct_iff decoder;
    dec_output : decoder_output_correct decoder;
    dec_increasing : decoder_strictly_increasing decoder;
    dec_projects : decoder_projects decoder;
  }.
```
A primeira propriedade afirma que todo `decoder` aceita a lista vazia. A segunda afirma que do _code point_ emitido pelo `decoder` deve ser válido. A terceira fala que todo input válido deve ser aceito. A quarta propriedade afirma sobre a ordenação entre bytes e _code points_, assim como no `decoder`. A quinta propriedade é uma propriedade de comutação para desconstruir listas em listas menores.

Com essas duas definições, a especificação UTF-8 completa para um par codificador e decodificador é o par que contém a especificação para o codificador e decodificador separadamente. Por serem disjuntos, é possível mostrar que quaisquer `encoder` e `decoder` são corretos mostrando que as regras valem para eles separadamente.
```coq
Record utf8_spec encoder decoder := {
    encoder_spec_compliant : utf8_encoder_spec encoder;
    decoder_spec_compliant : utf8_decoder_spec decoder;
  }.
```

Para ter certeza de que a especificação está correta, é necessário provar teoremas sobre ela. Como visto anteriormente, a propriedades principal que formará o cerne da corretude da especificação é de que todo par `(encoder, decoder)` que implemente `utf8_spec encoder decoder` deve necessariamente ser inverso um do outro.

Por ambos o codificador e decodificador serem _parser_ parciais, é preciso considerar que nem toda entrada irá ser aceita, e isso é levado em conta da seguinte forma: toda entrada deve necessariamente ter um prefixo UTF-8 válido -- que pode ser a lista vazia --  de forma que o prefixo válido deve ser a entrada para o processador dual.

```coq
Theorem utf8_spec_encoder_decoder_inverse : forall encoder decoder,
    utf8_spec encoder decoder ->
    forall codes bytes codes_suffix,
      encoder codes = (bytes, codes_suffix) ->
      exists codes_prefix, decoder bytes = (codes_prefix, nil) /\ codes = (codes_prefix ++ codes_suffix)%list.

Theorem utf8_spec_decoder_encoder_inverse_strong : forall encoder decoder,
    utf8_spec encoder decoder ->
    forall codes bytes bytes_suffix,
      decoder bytes = (codes, bytes_suffix) ->
      exists bytes_prefix, encoder codes = (bytes_prefix, nil) /\ bytes = (bytes_prefix ++ bytes_suffix)%list.
Proof.
```
Isto é, se `encoder codes = (bytes, codes_suffix)`, então necessariamente deve existir um prefixo `codes_prefix` tal que `decoder bytes = (codes_prefix, [])` e `codes = codes_prefix ++ codes_suffix`.

Para provar essas propriedades, muito trabalho é necessário. Intuitivamente, a prova é inteiramente baseada no fato de que ordenação implica em existir apenas uma função que respeite o mapeamento entre bytes e _code points_, entretanto isso não é nem um pouco óbvio. Assim, é necessário mostrar esse fato para que possa ser utilizado nas provas seguintes.

== Ordenações em conjuntos finitos

Para utilizar a ordenação produtivamente na prova, precisamos mostrar que exigir a ordenação é equivalente a completamente especificar a função de mapeamento. Para isso, é interessante considerar o conjunto de inteiros que esses mapeiam, pois provas sobre inteiros são mais fáceis de entender e manipular.

Tanto `valid_codepoint` quanto `valid_codepoint_representation` são propriedades que formam conjuntos finitos de exato mesmo tamanho (`0x10FFFF - 0x800` elementos, o número de _code points_ válidos). Por serem conjuntos finitos, é possível assinalar um inteiro para cada elemento, seu *índice*. Provar que a ordenação implica em apenas uma função significa provar que *existe apenas um mapeamento ordenado entre conjuntos finitos de mesmo tamanho*.

#quote(block: true, [Definição: o *índice* de um _code point_ é o número que representa a posição desse na ordenação. ])

Como o conjunto de _code points_ válidos possui uma descontinuidade no intervalo `U+D800..U+DFFF`, esse índice pode ser entendido como o próprio valor do _code point_ quando é menor que `U+D800`, e valor do _code point_ subtraido de `0x800` quando maior, de forma que $"index"("U+D7FF") = 1 + "index"("U+E000")$. Assim, fica claro que o conjunto de índices é exatamente o intervalo de inteiros entre `0 <= n < (0x10FFFF - 0x800)`.

#quote(block: true, [Definição: o *índice* de uma sequência de bytes é o índice do _code point_ que essa representa. ])

Com essas definições, fica claro que é possível mapear cada _code point_ e cada sequência de bytes em um inteiro unicamente, através das funções de `nth_valid_codepoint` -- que retorna o enésimo _code point_ válido dado seu índice -- e `nth_valid_codepoint_representation` -- que retorna a sequência de bytes do enésimo _code point_ válido. Além disso, o mapeamento em índices apenas pula descontinuidades, então esse deve ser ordenado.

Como queremos que os codificadores e decodificadores sejam inversos, é natural considerar que as funções de índices são inversíveis. De fato, ambas formam bijeções com o conjunto dos índices, e preservam a ordenação entre elementos, e portanto podem ser consideradas isomorfismos ordenados entre o cojunto de _code points_/sequências de bytes e o conjunto dos índices. No mais, os codificadores e decodificadores, segundo a especificação, também são formam uma bijeção ordenada, dessa vez diretamente entre _code points_ válidos e sequências de bytes.

Assim, a prova crucial para utilizar a ordenação consiste em mostrar que quaisquer dois codificadores e decodificadores que seguem a especificação corretamente devem se comportar como se consultassem `nth_valid_codepoint` e `nth_valid_codepoint_representation` internamente. Informalmente, é equivalente a provar que todo codificador deve transformar o enésimo _code point_ na enésima sequência de bytes.

Para formalizar essa noção, é necessário definir o que são isomorfismos parciais ordenados. Primeiro, são definidos morfismos parciais:
```coq
Definition interval (count n : Z) : Prop :=
  (0 <= n /\ n < count)%Z.

Record PartialMorphism {X Y}
  (domain : X -> Prop) (range : Y -> Prop) (f : X -> option Y) : Prop :=  {
    always_in_range : forall x y, domain x -> f x = Some y -> range y;
    not_domain_none: forall x, f x = None -> (not (domain x))
  }.

Definition and_then {X Y Z}
  (f : X -> option Y) (g : Y -> option Z) : X -> option Z :=
  fun x =>
    match (f x) with
    | Some y => (g y)
    | None => None
    end.

Definition pointwise_equal {X Y}
  (domain : X -> Prop) (f g : X -> option Y) : Prop :=
  forall x, domain x -> f x = g x.
```

Isto é, um morfismo parcial é uma função `f: X -> option Y` que possui duas propriedades, `domain` e `range`, de forma que sempre que `x` está no domínio -- `domain x` -- e `f x = Some y` para algum `y`, então `y` está na imagem -- `range y`. Note que não é necessário provar que `f x` sempre é `Some`, pois é possível de provar isso utilizando `not_domain_none`:

```coq
Theorem partial_morphism_elimination {X Y}
  {domain : X -> Prop} {range : Y -> Prop} {f : X -> option Y} :
  PartialMorphism domain range f ->
  forall (x : X),
    domain x ->
  exists y,
    ((range y) /\ (f x = Some y)).
Proof.
  intros [f_some f_none] x domain_x.
  destruct (f x) as [y|] eqn:f_x.
  - exists y. repeat split. apply (f_some x y); assumption.
  - apply f_none in f_x. apply f_x in domain_x. exfalso. auto.
Qed.
```

Vale ressaltar que só é exigido que `y` esteja na imagem quando `x` está no domínio, o que significa que `f` pode retornar `Some` para elementos fora do domínio. Isso é feito para suportar certas definições naturais, como que `fun x => Some x` é a função identidade, bem como provar que essa é um automorfismo ordenado de todo conjunto. Isso também significa que não é possível provar `domain x` dado `f x = Some y`.

A definição `pointwise_equal f g` é utilizada no lugar da igualdade `f = g`, pois provar igualdade de funções em Coq a partir da igualdade de elementos não é possível; isto é, não é possível provar que `f = g` com a hipótese de que `pointwise_equal f g` sem adicionar axiomas externos (extensionalidade funcional).

Com isso, definimos o que é um isomorfismo parcial:
```coq
Record PartialIsomorphism {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (to: T1 -> option T2) (from: T2 -> option T1) := {
    from_morphism : PartialMorphism domain range to;
    to_morphism: PartialMorphism range domain from;
    from_to_id : pointwise_equal domain (and_then to from) (fun x => Some x);
    to_from_id : pointwise_equal range (and_then from to) (fun x => Some x);
  }.
```

Um isomorfismo parcial é um par de morfismos `from` e `to` que mapeiam entre conjuntos `T1` e `T2`, junto de provas de que a composição deles dá a identidade. 

Para encapsular a ordenação, definimos a noção de conjunto ordenado, que é um tipo `T` munido de uma operação de comparação `compare` que respeita as seguintes propriedades:
```coq
Record Ordered {T} (compare: T -> T -> comparison) := {
    eq : forall t1 t2, compare t1 t2 = Eq <-> t1 = t2;
    antisym : forall t1 t2, compare t1 t2 = CompOpp (compare t2 t1);
    trans : forall t1 t2 t3 res,
              compare t1 t2 = res ->
              compare t2 t3 = res ->
              compare t1 t3 = res;
  }.
```
Ou seja, para prova provar que um tipo `T` é ordenado, basta mostrar que existe uma relação de comparação em `T` reflexiva, antisimétrica e transitiva. Além disso, a noção de uma função `to` ser "crescente" é caracterizada da seguinte forma:
```coq
Definition increasing {T1 T2}
  (domain: T1 -> Prop) (compare1: T1 -> T1 -> comparison)
  (compare2: T2 -> T2 -> comparison) (to: T1 -> option T2) :=
  forall n n' m m',
    (domain n) -> (domain m) ->
    to n = Some n' ->
    to m = Some m' ->
    (compare1 n m) = (compare2 n' m').
```
Informalmente, uma função `f` é `increasing` se `compare1 n m = compare2 (f n) (f m)`, ou seja, se respeita a comparação entre quaisquer dois elementos. É necessário exigir que ambos `n` e `m` estejam no domínio, pois consideramos `f` como um morfismo parcial, que pode retornar `Some` para elementos de fora do domínio.

Por fim, definimos um isomorfismo parcial ordenado como um par de conjuntos ordenados `T1` e `T2` que possuem um isomorfismo parcial, e que ao menos um dos mapeamentos é `increasing`, por simplicidade, o `to`.
```coq
Record OrderedPartialIsomorphism {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) (from: T2 -> option T1)
   := {
    opi_ordered1 : @Ordered T1 compare1;
    opi_ordered2 : @Ordered T2 compare2;
    opi_isomorphism : @PartialIsomorphism T1 T2 domain range to from;
    opi_to_preserves_compare : increasing domain compare1 compare2 to;
  }.
```

Apenas precisamos provar que um deles é `increasing`, visto que é relativamente simples provar que o `from` é `increasing` em seu respectivo domínio. De fato, provamos esse teorema no futuro, e ele é parte necessária para provar o teorema principal.

Para entender o argumento principal da ordenação de isomorfismos, é útil considerar a seguinte estrutura de isomorfismos entre o conjunto dos inteiros menores que `count`.

#image("isomorphism.png")

Dados dois conjuntos ordenados `T1` e `T2`, bem como isomorfismos desses para `interval count`, não é difícil mostrar que compor `from0` com `to2` com `to1` forma um automorfismo do conjunto de índices. Além disso, como todas as funções intermediárias respeitam a ordenação de seus respectivos conjuntos, esse automorfismo deve ser ordenado. Mas o único morfismo parcial que sai do conjunto dos inteiros e chega no conjunto dos inteiros respeitando a ordenação é a função identidade! De fato, queremos mostrar que

#align(center, $lambda x. "Some" x = "and_then" "to0" ("and_then" "to2" "from1")$)

Para isso, precisamos provar 3 teoremas: que todo morfismo parcial ordenado é `pointwise_equal` com a identidade, que `and_then to0 (and_then to2 from1)` é um automorfismo de `interval count`, e que esse respeita a ordenação.

O primeiro passo é representado no seguinte teorema:

```coq
Theorem interval_ordered_automorphism_is_id :
  forall (n: Z),
  (0 <= n)%Z ->
  forall (to : Z -> option Z),
    PartialMorphism (interval n) (interval n) to ->
    increasing (interval n) Z.compare Z.compare to ->
    pointwise_equal (interval n) to (fun x => Some x).
```

A prova desse teorema é feita resolvida utilizando indução em `n`. O caso base é trivialmente resolvido, visto que temos na hipótese um elemento `x` tal que `0 <= x < 0`.

O passo indutivo se baseia em mostrar que necessariamente `to n = Some n`. Para isso, sabemos que n deve pelo menos algum elemento na imagem `interval (Z.succ n)`, uma vez que `n < Z.succ n` trivialmente, logo `to n = Some n'`. Também sabemos que `n'` é menor que `Z.succ n`, então podemos quebrar a prova em dois casos, `n' = n`, exatamente queremos mostrar, ou `n' < n`, onde precisamos derivar alguma incoerência.

Para mostrar que `n' < n` é falso, precisamos mostrar duas propriedades que nos permitem reduzir a imagem e o domínio de um automorfismo. A primeira delas nos diz quando podemos reduzir a imagem:
```coq
Lemma tighten_ordered_morphism (n m m' : Z) (to : Z -> option Z) :
  PartialMorphism (interval (Z.succ n)) (interval m) to ->
  increasing (interval (Z.succ n)) Z.compare Z.compare to ->
  interval m m' ->
  to n = Some m' ->
  PartialMorphism (interval (Z.succ n)) (interval (Z.succ m')) to.
```
Este teorema nos permite limitar a imagem do morfismo quando a `interval (Z.succ m')` quando sabemos que `to n = Some m'` e `m' < m`. Intuitivamente, isso é válido porque tudo que prometemos sobre o resultado é que ele faz parte da imagem, mas é possível escolher um `m` grande demais, de forma que o maior elemento do domínio não chegue até o maior elemento da imagem.

A segunda propriedade nos diz quando podemos restringir o domínio e a imagem ao mesmo tempo:
```coq
Lemma ordered_morphism_restriction (n m n' m' : Z) (to : Z -> option Z) :
  PartialMorphism (interval n) (interval m) to ->
  increasing (interval n) Z.compare Z.compare to ->
  interval n n' ->
  interval m m' ->
  to n' = Some m' ->
  PartialMorphism (interval n') (interval m') to.
```

Da mesma forma, podemos restringir `to` a um morfismo entre `interval n'` e `interval m'` se mostrarmos que o maior elemento do domínio, `n'`, mapeia em `m'`, que `n'` está contido em `interval n` e que `m'` está contido em `interval m`.

Para derivar a contradição, basta mostrar que não podemos restringir demais a imagem:
```coq
Theorem no_ordered_morphism_to_smaller_interval : forall (n m : Z) (to : Z -> option Z),
  (0 <= m)%Z ->
  (m < n)%Z ->
  PartialMorphism (interval n) (interval m) to ->
  increasing (interval n) Z.compare Z.compare to ->
  False.
```

Esse teorema afirma que não podemos restringir um automorfismo ordenado para uma imagem menor que o tamanho do domínio, pois algum elemento do dominío necessariamente deve ser ignorado nesse caso. Esse é provado por indução, utilizando os dois lemmas acima, mostrando que aplicar as restrições válidas sempre levam em contradições.

Com esse teorema, podemos mostrar que `n' < n` implica em podermos limitarmos a imagem do morfismo (por `tighten_ordered_morphism`), gerando um morfismo cuja imagem é menor que o domínio, o que é uma contradição.

Tendo provado `interval_ordered_automorphism_is_id`, podemos provar o seguinte teorema:
```coq
Theorem finite_partial_isomorphism_unique {T0 T1} (count: Z) (range0: T0 -> Prop) (range1: T1 -> Prop) compare0 compare1:
  (0 <= count)%Z ->
  forall from0 from1 to0 to1 to2,
  OrderedPartialIsomorphism (interval count) range0 Z.compare compare0 to0 from0 ->
  OrderedPartialIsomorphism (interval count) range1 Z.compare compare1 to1 from1 ->
  PartialMorphism range0 range1 to2 ->
  increasing range0 compare0 compare1 to2 ->
  pointwise_equal range0 to2 (and_then from0 to1).
```

Como citado anteriormente, a prova desse é feita em 3 fases. Primeiro, mostramos que a composição de funções supracitada é um automorfismo de `interval count`:
```coq
Proof.
... 
assert (PartialMorphism (interval count) (interval count)
  (and_then to0 (and_then to2 from1))) as morphism.
```
Depois, mostramos que esse morfismo é crescente no mesmo intervalo:
```coq
...
assert (increasing (interval count) Z.compare Z.compare
              (and_then to0 (and_then to2 from1))) as increasing_composition.
```
E por fim, mostramos que podemos desfazer todas as operações com suas inversas chegando em `pointwise_equal to2 (and_then from0 to1)`, como queríamos demonstrar.

Como esse teorema em mãos, basta construir isomorfismos tais que `to0 = nth_valid_codepoint` e `to1 = nth_valid_codepoint_representation`, com `from0/from1` sendo suas respectivas inversas. Utilizando-o, conseguimos mostrar que qualquer outro morfismo `to2` -- em particular, um codificador que respeita a especificação -- deve ser `pointwise_equal` à composição dessas duas funções, mostrando sua unicidade. Trivialmente, a unicidade do decodificador também é resolvida apenas trocando a ordem dos isomorfismos.

== Índices de codepoints e de sequências de bytes

Assim, precisamos construir os isomorfismos supracitados. é necessário lembrar que o conjunto de índices exclui codepoints no intervalo `0xD800..0xDFFF`, ou seja, o índice deve "pular" esse intervalo. Assim, a única preocupação da função `nth_valid_codepoint` é somar `0x800` quando isso acontece:

```coq
Definition nth_valid_codepoint (n: Z) : option codepoint :=
  if n <? 0 then
    None
  else if n <? 0xd800 then
    Some n
  else if n <=? 0x10ffff - 0x0800 then
    Some (n + 0x0800)
  else
    None.
```

Para mostrar que essa função forma um isomorfismo parcial, as seguintes propriedades são provadas:
```coq
Lemma nth_valid_codepoint_is_some_iff_valid : forall code,
    (exists n, nth_valid_codepoint n = Some code) <->
      valid_codepoint code.

Lemma nth_valid_codepoint_none : forall n,
    nth_valid_codepoint n = None ->
    n < 0 \/ n > (0x10ffff - 0x800).

Lemma nth_valid_codepoint_increasing : forall n1 code1 n2 code2,
    nth_valid_codepoint n1 = Some code1 ->
    nth_valid_codepoint n2 = Some code2 ->
    Z.compare n1 n2 = Z.compare code1 code2.
```

A prova desses teoremas é omitida por brevidade, mas todas envolvem observar as comparações feitas em `nth_valid_codepoint` e utilizar a tática `lia` para casos específicos, que resolve relações na aritmética de Presburgo. Em especial, a prova de que respeita a comparação é feita considerando todas as possíveis maneiras que os `if`s podem se desdobrar, e mostrar que em todas elas as comparações são iguais.

Além disso, é necessário oferecer a função inversa dessa, que vai do índice do codepoint para o codepoint:
```coq
Definition inverse_nth_valid_codepoint (code: codepoint) : option Z :=
  if (code <? 0) then
    None 
  else if (code <? 0xd800) then
    Some code
  else if (code <=? 0x10ffff)%Z then
    Some (code - 0x0800)%Z
  else
    None.
```

Bem como provar que ambas são inversas:
```coq
Lemma nth_valid_codepoint_invertible : forall code n,
    nth_valid_codepoint n = Some code <->
      inverse_nth_valid_codepoint code = Some n /\ valid_codepoint code.
```

Assim, é possível provar que essa função forma um isomorfismo parcial ordenado, construindo um elemento do seguinte tipo:
```coq
Definition codepoint_nth_isomorphism : OrderedPartialIsomorphism (interval (0x10ffff - 0x7ff)) valid_codepoint Z.compare codepoint_compare nth_valid_codepoint inverse_nth_valid_codepoint.
```
Recapitulando, `codepoint_nth_isomorphism` é a prova de que o par (`nth_valid_codepoint`, `inverse_nth_valid_codepoint`) formam um isomorfimo com o conjunto de índices, e esse isomorfismo respeita a ordenação de codepoints e a ordenação de índices. A construção dessa prova utiliza todos os lemmas supracitados, bem como a prova de que o conjunto dos inteiros é um conjunto ordenado:
```coq
Definition ZOrder : @Ordered Z Z.compare.
  split. apply Z.compare_eq_iff. intros. apply Z.compare_antisym.
  intros. destruct res.
  - apply Z.compare_eq_iff in H, H0. subst. apply Z.compare_refl.
  - apply Zcompare.Zcompare_Lt_trans with (m := t2); assumption.
  - apply Zcompare.Zcompare_Gt_trans with (m := t2); assumption.
Qed.
```

Após isso, é necessário definir o mesmo para `nth_valid_code_representation`.
```coq
Definition nth_valid_codepoint_representation (n: Z) : option byte_str :=
  let n := if Z.ltb n 0xd800 then n else n + 0x800 in
  if (n <? 0) then
    None
  else if (n <=? 127) then
    Some [ n ]
  else if (n <=? 0x7ff) then
    let b1 := n / 64 in
    let b2 := n mod 64 in
    Some [ 192 + b1; 128 + b2]
  else if (n <=? 0xffff) then
    let r := n / 64 in
    let b1 := r / 64 in
    let b2 := r mod 64 in
    let b3 := n mod 64 in
    Some [ 224 + b1; 128 + b2; 128 + b3]
  else if (n <=? 0x10ffff) then
    let r1 := n / 64 in
    let r2 := r1 / 64 in
    let b1 := r2 / 64 in
    let b2 := r2 mod 64 in
    let b3 := r1 mod 64 in
    let b4 := n mod 64 in
    Some [ 240 + b1; 128 + b2; 128 + b3; 128 + b4]
  else
    None.
```

E provar os mesmos lemmas:
```coq
Lemma nth_valid_codepoint_representation_spec: forall bytes,
    (exists n, nth_valid_codepoint_representation n = Some bytes) <->
      valid_codepoint_representation bytes.

Lemma nth_valid_codepoint_representation_none : forall n : Z,
    nth_valid_codepoint_representation n = None -> 
    n < 0 \/ n > (1114111 - 2048).

Lemma nth_valid_codepoint_representation_compare_compat: forall n1 n2 bytes1 bytes2,
    nth_valid_codepoint_representation n1 = Some bytes1 -> 
    nth_valid_codepoint_representation n2 = Some bytes2 -> 
    Z.compare n1 n2 = bytes_compare bytes1 bytes2.
```

A prova desses é mais complexa, pois a função que mapeia o índice na sequência de bytes equivalente é muito mais complexa. Para facilitar a análise, táticas especiais foram criadas para automatizar a resolução de casos parecidos utilizando a tática `lia`.

Também é necessário desenvolver a função que calcula o índice do codepoint a partir da sequência de bytes.

```coq
Definition inverse_nth_valid_codepoint_representation (bytes: byte_str) : option Z :=
  let between b lo hi := andb (lo <=? b) (b <=? hi) in 
  match bytes with
  | [b] => if between b 0 127 then Some b else None
  | [b1; b2] =>
      if andb (between b1 0xc2 0xdf) (between b2 0x80 0xbf) then
        Some ((b1 mod 64) * 64 + (b2 mod 64))
      else None
  | [b1; b2; b3] =>
      let fst := andb (andb (b1 =? 0xe0) (between b2 0xa0 0xbf)) (between b3 0x80 0xbf) in
      let snd := andb (andb (between b1 0xe1 0xec) (between b2 0x80 0xbf)) (between b3 0x80 0xbf) in
      let trd := andb (andb (b1 =? 0xed) (between b2 0x80 0x9f)) (between b3 0x80 0xbf) in
      let frth := andb (andb (between b1 0xee 0xef) (between b2 0x80 0xbf)) (between b3 0x80 0xbf) in
      let n := ((b1 - 224) * 64 * 64) + (b2 mod 64) * 64 + (b3 mod 64) in
      if orb (orb fst snd) trd then
        Some n
      else if frth then
        Some (n - 2048)
      else 
        None
  | [b1; b2; b3; b4] =>
      let fst := andb (andb (andb (b1 =? 0xf0) (between b2 0x90 0xbf)) (between b3 0x80 0xbf)) (between b4 0x80 0xbf) in
      let snd := andb (andb (andb (between b1 0xf1 0xf3) (between b2 0x80 0xbf)) (between b3 0x80 0xbf)) (between b4 0x80 0xbf) in
      let trd := andb (andb (andb (b1 =? 0xf4) (between b2 0x80 0x8f)) (between b3 0x80 0xbf)) (between b4 0x80 0xbf) in
      if orb (orb fst snd) trd then
        Some ((b1 - 240) * 64 * 64 * 64 + (b2 mod 64) * 64 * 64 + (b3 mod 64) * 64 + (b4 mod 64) - 0x800)
      else None
  | _ => None
  end.
```

Vale notar que as operações que essa executa são exatamente as mesmas operações dadas em `naive_utf8_map`, mas dessa vez, a corretude dessas operações é checada no fato de que essa é a inversa da `nth_valid_codepoint_representation`:

```coq
Lemma nth_valid_codepoint_representation_invertible : forall n bytes,
    nth_valid_codepoint_representation n = Some bytes ->
      inverse_nth_valid_codepoint_representation bytes = Some n.

Lemma inverse_nth_valid_codepoint_representation_invertible : forall bytes n,
    valid_codepoint_representation bytes ->
    inverse_nth_valid_codepoint_representation bytes = Some n ->
    nth_valid_codepoint_representation n = Some bytes.
```

Por fim, também é necessário provar que o conjunto de sequências de bytes é ordenado, de acordo com a comparação lexicográfica.

```coq
Definition BytesOrder : Ordered bytes_compare.
Proof.
  unfold bytes_compare.
  split.
  - apply list_compare_refl. apply Z.compare_eq_iff.
  - intros.
    apply list_compare_antisym. apply Z.compare_eq_iff. apply Z.compare_antisym.
  - intros.
    apply list_compare_trans with (ys:=t2); try assumption.
    + apply Z.compare_eq_iff.
    + intros. destruct c.
      -- apply Z.compare_eq_iff in H1, H2. subst. apply Z.compare_refl.
      -- apply Zcompare.Zcompare_Lt_trans with (m := y); assumption.
      -- apply Zcompare.Zcompare_Gt_trans with (m := y); assumption.
    + apply Z.compare_antisym.
Qed.
```

Assim, é possível provar que o par (`nth_valid_codepoint_representation`, `inverse_nth_valid_codepoint_representation`) forma um isomorfismo com o conjunto dos inteiros de `0x10ffff - 0x7ff`, e que esse isomorfismo respeita a ordenação:
```coq
Theorem valid_codepoint_representation_isomorphism :
    OrderedPartialIsomorphism (interval (0x10ffff - 0x7ff)) valid_codepoint_representation Z.compare bytes_compare nth_valid_codepoint_representation inverse_nth_valid_codepoint_representation.
```

== Corretude da especificação

Desde o início, o objetivo de mostrar essas propriedades de ordenação e de índice é utilizar `finite_partial_isomorphism_unique` para provar os seguintes teoremas:
```coq
Lemma utf8_spec_implies_encoder_maps_nth_to_nth : forall encoder,
    utf8_encoder_spec encoder ->
    forall code bytes,
      encoder [code] = (bytes, []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_codepoint_representation n = Some bytes.

Lemma utf8_spec_implies_decoder_maps_nth_to_nth : forall decoder,
    utf8_decoder_spec decoder ->
    forall code bytes,
      decoder bytes = ([code], []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_codepoint_representation n = Some bytes.
```

Isto é, quando um codificador aceita um codepoint, então o resultado é a sequência de bytes com o índice equivalente. Da mesma forma, quando o decodificador aceita uma sequência de bytes, então o resultado é o codepoint com o índice equivalente. 

Para utilizar o teorema de ordenação nessa prova, é necessário construir morfismos parciais (que retornam `option` ao invés de listas) a partir de codificadores e decodificadores:
```coq
Definition encoder_to_option (encoder: encoder_type) code :=
  match encoder [code] with
  | (bytes, []) => Some bytes
  | _ => None
  end.

Definition decoder_to_option (decoder: decoder_type) bytes :=
  match decoder bytes with
  | ([code], []) => Some code
  | _ => None
  end.
```

Assim, os seguintes lemmas sobre `encoder` e `decoder` são provados, para que possam ser utilizados nas provas:
```coq
Lemma encoder_partial_morphism : forall encoder,
    utf8_encoder_spec encoder -> 
    partial_morphism valid_codepoint valid_codepoint_representation (encoder_to_option encoder).

Lemma decoder_partial_morphism : forall decoder,
    utf8_decoder_spec decoder ->
    partial_morphism valid_codepoint_representation valid_codepoint (decoder_to_option decoder).

Lemma encoder_to_option_increasing : forall encoder,
    utf8_encoder_spec encoder ->
    increasing valid_codepoint Z.compare bytes_compare (encoder_to_option encoder).

Lemma decoder_to_option_increasing: forall decoder,
    utf8_decoder_spec decoder ->
    increasing valid_codepoint_representation bytes_compare Z.compare (decoder_to_option decoder).
```

Todos esses lemmas apenas estendem as propriedades dos codificadores e decodificadores para o morfismo parcial. Com os lemmas de mapeamento de `n` pra `n` em mãos, é trivial mostrar que tanto o `encoder` quanto o `decoder` devem ser inversos no caso de apenas um codepoint:

```coq
Theorem utf8_spec_encoder_decoder_inverse_single: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      encoder [code] = (bytes, []) ->
      decoder bytes = ([code], []).

Theorem utf8_spec_decoder_encoder_inverse_single: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      decoder bytes = ([code], []) ->
      encoder [code] = (bytes, []).
```

Provar esses teoremas se reduz a aplicar o teorema de mapeamento `n` em `n`, e mostrar que podemos transformar índices em _code points_ / bytes utilizando as inversas. Esses teoremas são suficientes para provar o teorema da corretude da especificação do codificador:
```coq
Theorem utf8_spec_encoder_decoder_inverse : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall codes bytes codes_suffix,
      encoder codes = (bytes, codes_suffix) ->
      exists codes_prefix, decoder bytes = (codes_prefix, nil) /\ codes = (codes_prefix ++ codes_suffix)%list.
```

Esse é trivialmente provado por indução na lista de entrada, aplicando `utf8_spec_encoder_decoder_inverse_single` no _code point_ extraído.

Para provar a corretude do decodificador, mais trabalho é necessário, visto que indução na lista de entrada não é uma estratégia suficiente. Ao invés isso, gostaríamos de fazer a indução na lista de _code points_ da saída, visto que essa é muito mais simples de entender.

Com esse objetivo, provamos que o decodificador tem uma propriedade dual à projeção do codificador:

```coq
Theorem utf8_spec_decoder_project_dual : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall xs ys bytes bytes_suffix,
      decoder bytes = (xs ++ ys, bytes_suffix) ->
      (exists bytes1 bytes2,
          decoder bytes1 = (xs, []) /\ 
            decoder bytes2 = (ys, []) /\
            bytes = bytes1 ++ bytes2 ++ bytes_suffix).
```

Com essa propriedade, podemos provar por indução que ambos são inversos:

```coq
Theorem utf8_spec_decoder_encoder_inverse: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall codes bytes bytes_suffix,
      decoder bytes = (codes, bytes_suffix) ->
      exists bytes_prefix, encoder codes = (bytes_prefix, nil) /\ bytes = (bytes_prefix ++ bytes_suffix)%list.
```

Utilizamos a propriedade dual da projeção para separar `decoder bytes = (code :: codes, suffix)` em `decoder bytes1 = ([code], [])`, onde podemos aplicar o teorema de que são inversos para um elemento.

#pagebreak()

= Implementação

Com a especificação feita, a implementação de um codificador e decodificador práticos é relativamente simples. Para implementar o codificador, primeiro é definida uma função que mapeia um codepoint numa sequência de bytes:
```coq
Definition utf8_encode_codepoint (n: codepoint) : @option (list byte) :=
  if (n <? 0) then
    None
  else if (n <=? 127) then
    Some [ n ]
  else if (n <=? 0x7ff) then
    let b1 := n / 64 in
    let b2 := n mod 64 in
    Some [ 192 + b1; 128 + b2]
  else if (andb (n <=? 0xffff) (orb (n <? 0xd800) (n >? 0xdfff))) then
    let r := n / 64 in
    let b1 := r / 64 in
    let b2 := r mod 64 in
    let b3 := n mod 64 in
    Some [ 224 + b1; 128 + b2; 128 + b3]
  else if (andb (n <=? 0x10ffff) (n >? 0xffff)) then
    let r1 := n / 64 in
    let r2 := r1 / 64 in
    let b1 := r2 / 64 in
    let b2 := r2 mod 64 in
    let b3 := r1 mod 64 in
    let b4 := n mod 64 in
    Some [ 240 + b1; 128 + b2; 128 + b3; 128 + b4]
  else
    None.
```
Assim, o codificador é definido como uma função que recursivamente mapeia o mapeamento acima, parando quando a lista acaba ou quando o mapeamento retorna `None`.
```coq
Fixpoint utf8_encode (unicode: unicode_str) : (list byte) * (list codepoint) :=
  match unicode with
  | [] => ([], [])
  | code :: unicode_rest =>
      match utf8_encode_codepoint code with
      | None => ([], code :: unicode_rest)
      | Some bytes => 
          let (bytes_rest, unicode_rest) := utf8_encode unicode_rest in
          (bytes ++ bytes_rest, unicode_rest)
      end
  end.
```

// https://bjoern.hoehrmann.de/utf-8/decoder/dfa/
Para implementar o decodificador, é utilizado um autômato de estado finito. Um DFA pode ser derivado observando cada linha da @UTF8_bytes, e considerando quais caracteres podem ser lidos em cada parte.

#image("dfa-bytes.png")

A partir desse grafo, define-se o conjunto de possíveis estados, e uma enumeração de todos os possíveis estados úteis que aparecem no grafo:
```coq
Inductive parsing_state :=
  Initial
| Expecting_1_80_BF
| Expecting_2_80_BF
| Expecting_3_80_BF
| Expecting_2_80_9F
| Expecting_2_A0_BF
| Expecting_3_90_BF
| Expecting_3_80_8F.

Inductive byte_range :=
| Range_00_7F 
| Range_80_8F
| Range_90_9F
| Range_A0_BF
| Range_C2_DF
| Byte_E0      
| Range_E1_EC
| Byte_ED
| Range_EE_EF
| Byte_F0
| Range_F1_F3
| Byte_F4
.

Definition byte_range_dec (b: byte) : option byte_range :=
  if b <? 0 then
    None
  else if b <=? 0x7f then
    Some Range_00_7F
  else if b <=? 0x8f then
    Some Range_80_8F
  else if b <=? 0x9f then
    Some Range_90_9F
  else if b <=? 0xbf then
    Some Range_A0_BF
  else if b <=? 0xc1 then
    None
  else if b <=? 0xdf then
    Some Range_C2_DF
  else if b  =? 0xe0 then
    Some Byte_E0
  else if b <=? 0xec then
    Some Range_E1_EC
  else if b  =? 0xed then
    Some Byte_ED
  else if b <=? 0xef then
    Some Range_EE_EF
  else if b  =? 0xf0 then
    Some Byte_F0
  else if b <=? 0xf3 then
    Some Range_F1_F3
  else if b  =? 0xf4 then
    Some Byte_F4
  else
    None.
```

Também são definidas funções auxiliares para representar as operações de extração de bits relevantes.
```coq
Definition push_bottom_bits (carry: codepoint) (b: byte): codepoint :=
  carry * 64 + (b mod 64).

Definition extract_7_bits (b: byte) : codepoint :=
  b mod 128.

Definition extract_5_bits (b: byte) : codepoint :=
  b mod 32.

Definition extract_4_bits (b: byte) : codepoint :=
  b mod 16.

Definition extract_3_bits (b: byte) : codepoint :=
  b mod 8.
```
Por fim, é definida a função `next_state`, que calcula o próximo estado do DFA a partir do estado atual e do byte visto. Para representar o fim de um codepoint, é criado o tipo `parsing_result`:
```coq
Inductive parsing_result :=
  Finished (codep: codepoint)
| More (state: parsing_state) (acc: codepoint).

Definition next_state (state: parsing_state) (carry: codepoint) (b: byte) : @option parsing_result :=
  match (state, byte_range_dec b) with
  | (Initial, Some Range_00_7F) => Some (Finished (extract_7_bits b))
  | (Initial, Some Range_C2_DF) => Some (More Expecting_1_80_BF (extract_5_bits b))
  | (Initial, Some Byte_E0)     => Some (More Expecting_2_A0_BF (extract_4_bits b))
  | (Initial, Some Range_E1_EC)
  | (Initial, Some Range_EE_EF) => Some (More Expecting_2_80_BF (extract_4_bits b))
  | (Initial, Some Byte_ED)     => Some (More Expecting_2_80_9F (extract_4_bits b))
  | (Initial, Some Byte_F0)     => Some (More Expecting_3_90_BF (extract_3_bits b))
  | (Initial, Some Range_F1_F3) => Some (More Expecting_3_80_BF (extract_3_bits b))
  | (Initial, Some Byte_F4)     => Some (More Expecting_3_80_8F (extract_3_bits b))
  | (Initial, _) => None
  | (Expecting_1_80_BF, Some Range_A0_BF)
  | (Expecting_1_80_BF, Some Range_90_9F)
  | (Expecting_1_80_BF, Some Range_80_8F) => Some (Finished (push_bottom_bits carry b))
  | (Expecting_2_80_BF, Some Range_80_8F)
  | (Expecting_2_80_BF, Some Range_90_9F)
  | (Expecting_2_80_9F, Some Range_80_8F)
  | (Expecting_2_80_9F, Some Range_90_9F)
  | (Expecting_2_80_BF, Some Range_A0_BF) => Some (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_BF, Some Range_80_8F)
  | (Expecting_3_80_BF, Some Range_90_9F)
  | (Expecting_3_80_BF, Some Range_A0_BF)
  | (Expecting_3_90_BF, Some Range_90_9F)
  | (Expecting_3_90_BF, Some Range_A0_BF)
  | (Expecting_3_80_8F, Some Range_80_8F) => Some (More Expecting_2_80_BF (push_bottom_bits carry b))
  | (Expecting_2_A0_BF, Some Range_A0_BF) => Some (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_8F, Some Range_90_9F)
  | (Expecting_3_80_8F, Some Range_A0_BF) => None
  | _ => None
  end.
```

A função do decodificador, então, é uma função que recursivamente calcula o próximo estado utilizando `next_state`. Quando o resultado é um codepoint finalizado, a função volta para o estado inicial e começa a ler um novo codepoint.
```coq
Fixpoint utf8_dfa_decode_rec (bytes: list byte) (carry: codepoint) (state: parsing_state) (consumed: list byte)
  : unicode_str * (list byte) :=
  match bytes with
  | nil => ([], consumed)
  | cons b rest =>
      match next_state state carry b with
      | Some (Finished codep) =>
          let (vals, rest) := utf8_dfa_decode_rec rest 0x00 Initial [] in
          (codep :: vals, rest)
      | Some (More state codep) =>
          utf8_dfa_decode_rec rest codep state (consumed ++ [b])
      | None => ([], consumed ++ bytes)
      end
  end.

Definition utf8_dfa_decode (bytes: list byte) : unicode_str * (list byte) :=
  utf8_dfa_decode_rec bytes 0x00 Initial [].
```

Note que, pelas restrições de ser um _parser_ parcial, é necessário guardar os bytes consumidos equivalentes ao codepoint atual, de modo a não jogar fora bytes se apenas um da sequência for inválido. Isso é necessário para provar que essa função siga a especificação dada anteriromente.

Como reforçado anteriormente, a corretude da implementação está inteiramente baseada em provar que ambos codificador e decodificador seguem a especificação desenvolvida. Dado todo o desenvolvimento, fica extremamente claro o significado de "provar que segue a especificação": construir um elemento cujo tipo é `utf8_spec utf8_encode utf8_dfa_decode`.

Para fazer isso, basta construir dois elementos, um de tipo `utf8_encode_spec utf8_encode`, e outro de tipo `utf8_decode_spec utf8_dfa_decode`. Como visto anteriormente, isso significa provar os cinco lemmas para `utf8_encode` e cinco lemmas para `utf8_decode`.

== Provando a corretude do codificador

A prova de que `utf8_encode [] = ([], [])` se reduz a computar o lado esquerdo e provar a igualdade:
```coq
Lemma utf8_encode_nil : encoder_nil utf8_encode.
Proof.
  reflexivity.
Qed.
```
Para provar `encoder_input_correct_iff`, é útil mostrar primeiro que a função que transforma um codepoint em bytes (`utf8_encode_codepoint`) está correta:

```coq
Lemma utf8_encode_codepoint_input : forall code,
    valid_codepoint code <->
    exists bytes, utf8_encode_codepoint code = Some bytes.
Proof.
  intro code; split. 
  - intro valid_code.
    destruct (utf8_encode_codepoint code) as [bytes |] eqn:encode_code.
    + exists bytes. reflexivity.
    + unfold utf8_encode_codepoint in encode_code.
      destruct valid_code as [c1 [c2 c3]].
      unfold codepoint_less_than_10ffff in c1.
      unfold codepoint_is_not_surrogate in c2.
      unfold codepoint_not_negative in c3.
      crush_comparisons; try discriminate; lia.
  - intros [bytes encode_code].
    unfold utf8_encode_codepoint in encode_code.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative.
    crush_comparisons; try discriminate; lia.
Qed.
```
Vale ressaltar que essa prova mostra uma das forças principais do Coq: táticas de automação customizadas. A tática `crush_comparisons` fora criada especificamente para reescrever hipóteses que contém `if _ then _ else` e destruí-las em dois _goals_, um onde se prova o caso em que a condição é verdadeira, e outro onde a condição é falsa. 
```coq
Ltac crush_comparisons :=
  repeat match goal with
    | [G: context[if (?a <=? ?b)%N then _ else _] |- _] => 
        let l := fresh "less_than_eq" in
        destruct (a <=? b)%N eqn:l; [apply Z.leb_le in l| apply Z.leb_nle in l]
    | [G: context[if (?a <? ?b)%N then _ else _] |- _] => 
        let l := fresh "less_than" in
        destruct (a <? b)%N eqn:l; [apply Z.ltb_lt in l| apply Z.ltb_nlt in l]
    | [G: context[if (?a >? ?b)%N then _ else _] |- _] => 
        rewrite Z.gtb_ltb in G
    | [G: context[if (andb ?a ?b) then _ else _] |- _] =>
        rewrite Bool.andb_if in G
    | [G: context[if (orb ?a ?b) then _ else _] |- _] =>
        rewrite Bool.orb_lazy_alt in G
    end.
```

Assim, não é necessário manualmente provar cada um dos casos utilizando as provas matemáticas específicas, o que é muito mais trabalhoso. Com esse lemma, a prova de que todo codepoint unitário é levado em uma sequência de bytes, e toda sequência de bytes tem um codepoint equivalente, é simples:
```coq
Lemma utf8_encode_correct : encoder_input_correct_iff utf8_encode.
Proof.
  intros code. split.
  - intro valid_code.
    destruct (utf8_encode [code]) as [bytes rest] eqn: enc.
    exists bytes. apply pair_equal_spec. repeat split.
    simpl in enc.
    apply utf8_encode_codepoint_input in valid_code.
    destruct valid_code as [bytes2 enc_code]. rewrite enc_code in enc.
    inversion enc. reflexivity.
  - intros [bytes enc_code].
    simpl in enc_code.
    destruct (utf8_encode_codepoint code) as [bytes2 |] eqn:enc_single; [| discriminate].
    inversion enc_code. subst.
    apply utf8_encode_codepoint_input.
    exists bytes2. assumption.
Qed.
```

A prova de `utf8_encode_output`, que afirma que toda sequência de bytes deve ser `valid_codepoint_representation`, também é similarmente simples: basta descontruir a função em todos os possíveis casos em que um codepoint pode ser mapeado, e depois provar que todos eles estão certos utilizando `lia`. Para isso, outra tática customizada é utilizada, `add_bounds`, que adiciona provas sobre desigualdades envolvendo `mod` ao contexto, para que a tática `lia` possa provar teoremas envolvendo comparações.
```coq
Lemma utf8_encode_output : encoder_output_correct utf8_encode.
Proof.
  intros code.
  destruct (utf8_encode [code]) as [bytes rest] eqn:encode_single.
  simpl in encode_single.
  destruct (utf8_encode_codepoint code) as [bytes2 |] eqn:encode_code; [| inversion encode_single; split; reflexivity].
  assert (exists bytes, utf8_encode_codepoint code = Some bytes) as code_valid. exists bytes2. assumption.
  apply utf8_encode_codepoint_input in code_valid.
  unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in code_valid.
  destruct code_valid as [c1 [c2 c3]].
  inversion encode_single. rewrite app_nil_r in *. subst.
  unfold utf8_encode_codepoint in encode_code.
  crush_comparisons; try discriminate; try lia; rewrite <- some_injective in encode_code; subst.
  + apply OneByte. lia.
  + add_bounds (code mod 64). apply TwoByte; lia.
  + add_bounds (code mod 64).
    add_bounds ((code / 64) mod 64).
    destruct c2.
    * destruct (code / 64 / 64 =? 0) eqn:is_e0.
      -- apply ThreeByte1; lia.
      -- destruct (code <? 0xd000) eqn:code_less_d000.
         --- apply ThreeByte2. left. all: lia.
         --- apply ThreeByte3; lia.
    * apply ThreeByte2. right. all: lia.
  + add_bounds (code mod 64). add_bounds (code / 64 mod 64). apply ThreeByte2; try lia.
  + add_bounds (code mod 64).
    add_bounds (code / 64 mod 64).
    add_bounds ((code / 64 / 64) mod 64).
    destruct (code / 64 / 64 / 64 =? 0) eqn:is_f0.
    * apply FourBytes1; try lia.
    * destruct (code / 64 / 64 / 64 =? 4) eqn:is_f4.
      -- apply FourBytes3; try lia.
      -- apply FourBytes2; try lia.
Qed.
```

É interessante notar que os 5 _goals_ resultantes estão diretamente relacionados com as 5 maneiras que um `codepoint` pode ser considerado correto: uma maneira para cada intervalo de 1, 2 e 4 bytes, e 2 maneiras no intervalo de 3 bytes -- pode tanto ser menor que `0xDB00` quanto maior que `0xDFFF`.

A prova de que o codificador pode ser projetado corretamente sobre listas menores é trivial, e se resume a afirmar que concatenação de listas é comutativa:
```coq
Lemma utf8_encode_projects : encoder_projects utf8_encode.
Proof.
  intro xs. induction xs as [|x xs]; intros ys.
  - rewrite utf8_encode_nil. rewrite app_nil_l.
    destruct (utf8_encode ys). reflexivity.
  - rewrite <- app_comm_cons.
    unfold utf8_encode. fold utf8_encode.
    destruct (utf8_encode_codepoint x) as [bytes |]eqn:encode_x.
    + rewrite IHxs.
      destruct (utf8_encode xs). destruct (utf8_encode ys).
      destruct l0. rewrite app_assoc. reflexivity. reflexivity.
    + rewrite app_comm_cons. reflexivity.
Qed.
```

Por fim, o teorema de que `utf8_encode` é crescente é facilmente resolvido utilizando a combinação de `crush_comparisons` e `lia`. 

```coq
Lemma utf8_encode_increasing: encoder_strictly_increasing utf8_encode.
Proof.
  intros code1 code2 bytes1 bytes2 encode_code1 encode_code2.
  simpl in encode_code1, encode_code2.
  destruct (utf8_encode_codepoint code1) as [bytes1'|] eqn:enc_code1; [|inversion encode_code1].
  destruct (utf8_encode_codepoint code2) as [bytes2'|] eqn:enc_code2; [|inversion encode_code2]. rewrite app_nil_r in *.
  inversion encode_code1. inversion encode_code2. subst.
  clear encode_code1. clear encode_code2.
  unfold utf8_encode_codepoint in enc_code1, enc_code2.
  crush_comparisons; try discriminate; try lia; rewrite <- some_injective in enc_code1; rewrite <- some_injective in enc_code2; subst; unfold bytes_compare, list_compare.
  1: destruct (code1 ?= code2); reflexivity.
  all: (repeat match goal with
          | |- context[match ?a ?= ?b with | _ => _ end] =>
              let comp := fresh "compare" in
              add_bounds a; add_bounds b;
              destruct (Z.compare_spec a b) as [comp | comp | comp]
          end);
    match goal with
    | [|- (?n1 ?= ?n2 = Eq)] => apply Z.compare_eq_iff
    | [|- (?n1 ?= ?n2 = Lt)] => fold (Z.lt n1 n2)
    | [|- (?n1 ?= ?n2 = Gt)] => fold (Z.gt n1 n2)
    end; subst; try discriminate; lia.
Qed.
```
Na prova deste teorema há duas hipóteses contendo `utf8_encode` distintos no contexto, o que significa que `crush_comparisons` desconstrói em 289 casos distintos, a maioria deles com hipóteses inválidas, como `None = Some _`, ou `code1 < coe2` e `code2 < code1`. A sequência `try discriminate; try lia` resolvem essas imediatamente. Como resultado, sobram exatamente 25 = $5 * 5$ goals, o produto cartesiano de todas as possíveis maneiras que dois codepoints podem ser válidos, e todos esses involvem comparações entre elementos de mesmo tamanho, e são facilmente resolvidos por `lia`.

Por fim, é enunciada a prova de que essa função de fato segue a especificação dada anteriormente:

```coq
Theorem utf8_encode_spec_compliant : utf8_encoder_spec utf8_encode.
Proof.
  split.
  - apply utf8_encode_nil.
  - apply utf8_encode_increasing.
  - apply utf8_encode_correct.
  - apply utf8_encode_output.
  - apply utf8_encode_projects.
Qed.
```

== Provando a corretude do decodificador

Assim como no caso do codificador, provar que `utf8_dfa_decode [] = ([], [])` é trivialmente resolvido por `reflexivity`.

```coq
Lemma utf8_dfa_nil : decoder_nil utf8_dfa_decode.
Proof.
  reflexivity.
Qed.
```

Para provar que `utf8_dfa_decode` projeta sobre entradas válidas pode ser provado utilizando uma tática auxiliar `lia_simplify`, que tenta simplificar comparações quando `lia` consegue provar que essas devem ser verdadeiras ou falsas. Duas versões são dadas, `lia_simplify` que atua diretamente no _goal_, e `lia_simplify_hyp`, que atua em uma hipótese.
```coq
Ltac lia_simplify :=
  repeat match goal with
    | |- context[match (if ?cond then ?a else ?b) with | _ => _ end] =>
        ((replace cond with false by lia) || (replace cond with true by lia) || (destruct cond))
    end.

Ltac lia_simplify_hyp H :=
  repeat match type of H with
    | context[match (if ?cond then ?a else ?b) with | _ => _ end] =>
        (replace cond with false in H by lia)
            || (replace cond with true in H by lia)
            || let C := fresh "cond" in destruct cond eqn:C
    end.

Lemma utf8_dfa_projects : decoder_projects utf8_dfa_decode.
Proof.
  intros xs ys valid_xs.
  unfold utf8_dfa_decode.
  destruct valid_xs; simpl; unfold next_state, byte_range_dec; lia_simplify; 
    destruct (utf8_dfa_decode_rec ys 0 Initial []); reflexivity.
Qed.
```

Para os outros 3 teoremas, dois lemmas centrais sobre `utf8_dfa_decode` serão utilizados. O primeiro afirma que quando a o prefixo UTF-8 válido é `[]`, então a parte inválida deve ser igual à entrada dada a função:
```coq
Lemma utf8_dfa_decode_invalid: forall bytes suffix,
    utf8_dfa_decode bytes = ([], suffix) ->
    bytes = suffix.
Proof.
  intros bytes suffix decode_bytes.
  unfold utf8_dfa_decode in decode_bytes.
  destruct bytes as [| byte1 bytes].
  - simpl in decode_bytes. inversion decode_bytes. reflexivity.
  - repeat lazymatch goal with
           | [NextState: context[next_state ?state ?carry ?byte] |- _] =>
               unfold next_state in NextState;
               let range := fresh "range" in
               destruct (byte_range_dec byte) as [range|];
               [| inversion NextState; reflexivity];
               destruct range;
               try (inversion NextState; reflexivity)
           | [Decode: context[utf8_dfa_decode_rec (?byte :: ?rest) ?code ?state ?consumed] |- _] =>
               simpl in Decode
           | [Decode: context[utf8_dfa_decode_rec ?bytes 0 Initial ?consumed] |- _] =>
               destruct (utf8_dfa_decode_rec bytes 0 Initial); inversion Decode
           | [Decode: context[utf8_dfa_decode_rec ?bytes ?code ?state ?consumed] |- _] =>
               let byte := fresh "byte" in
               let rest := fresh "bytes" in
               destruct bytes as [| byte rest]; simpl in Decode; [inversion Decode; reflexivity|]
           end.
Qed.
```

Novamente, a estratégia dessa prova se resume em destruir todas as possíveis maneiras que uma sequência de bytes pode ser rejeitada, e mostrar que em todas elas `bytes = suffix`.

O segundo teorema afirma que, quando o resultado contém ao menos um _code point_ `code`, então esse deve ser válido, e deve haver um prefixo `prefix` UTF-8 válido tal que `utf8_decode prefix = ([code], [])`.
```coq
Lemma utf8_dfa_decode_prefix: forall bytes code codes suffix,
    utf8_dfa_decode bytes = (code :: codes, suffix) ->
    exists prefix rest,
      valid_codepoint code /\
        valid_codepoint_representation prefix /\ 
        utf8_dfa_decode prefix = ([code], []) /\
        utf8_dfa_decode rest = (codes, suffix) /\
        bytes = prefix ++ rest.
```

A prova desse lemma é significativamente mais complicada, dado que o objetivo é provar uma conjunção de 5 proposições. Ela pode ser entendida em duas fases: primeiro, todos as possíveis maneiras de que um `byte` pode ser considerado válido são separadas em diferentes _goals_; depois, as proposições são provadas utilizando táticas específicas, uma para cada afirmação da conjunção.

A combinação de `utf8_dfa_decode_invalid` e `utf8_dfa_decode_prefix` é tudo que é preciso para provar provas sobre `utf8_dfa_decode` utilizando indução. Como bytes que representam codepoints podem ter de 1 a 4 elementos de tamanho, provas de indução na lista de entrada são fracas demais para serem úteis, e é muito mais natural fazer a indução na lista de saída de _code points_. Assim, esses dois lemmas contém todas as propriedades cruciais que serão necessárias para provar os próximos teoremas.

A prova de que toda lista de saída de `utf8_dfa_decode` é `valid_utf8` é resolvida com uma simples indução na lista de _code points_ do resultado:
```coq
Lemma utf8_dfa_output : decoder_output_correct utf8_dfa_decode.
Proof.
  intros bytes suffix codes decode_bytes.
  generalize dependent bytes.
  induction codes as [| code codes].
  - split. constructor.
    exists []. repeat split. constructor.
    apply utf8_dfa_decode_invalid in decode_bytes.
    subst. reflexivity.
  - intros bytes decode_bytes.
    apply utf8_dfa_decode_prefix in decode_bytes as G.
    destruct G as [prefix [rest [valid_code [valid_prefix [decode_prefix [decode_rest bytes_eq]]]]]].
    apply IHcodes in decode_rest as G.
    destruct G as [valid_codes [prefix2 [decode_prefix2 [valid_prefix2 G]]]].
    subst. split.
    + apply Forall_cons. all: assumption.
    + exists (prefix ++ prefix2). repeat split.
      * rewrite utf8_dfa_projects. rewrite decode_prefix, decode_prefix2. reflexivity. assumption.
      * constructor. all: assumption.
      * rewrite app_assoc. reflexivity.
Qed.
```

Da mesma forma, provar que toda sequência de bytes é aceita pelo decodificador não é complicado, e se reduz a aplicar os lemmas descritos anteriormente.
```coq
Lemma utf8_dfa_input : decoder_input_correct_iff utf8_dfa_decode.
Proof.
  split.
  - intros bytes_valid.
    destruct bytes_valid; unfold utf8_dfa_decode; simpl; unfold next_state, byte_range_dec; lia_simplify; eexists; reflexivity.
  - intros [code decode_bytes].
    apply utf8_dfa_decode_prefix in decode_bytes as G.
    destruct G as [prefix [rest [code_valid [prefix_valid [decode_prefix [decode_rest bytes_eq]]]]]].
    subst.
    apply utf8_dfa_decode_invalid in decode_rest. subst. rewrite app_nil_r in *.
    assumption.
Qed.
```

Infelizmente, a prova de que `utf8_dfa_decode` é crescente é complexa, visto que a abordagem força bruta de desconstruir em todos os casos é demorada demais. Especificamente, existem 85 maneiras de uma sequência de bytes que representa um _code point_ ser aceita por `utf8_dfa_decode`, e dado que essa prova contém duas hipóteses que contém `utf8_dfa_decode`, o método força bruta resulta em $85 * 85 = 7225$ _goals_ diferentes, número grande demais para ser checado em pouco tempo pelo Rocq.

Por causa disso, é necessário reduzir o número de _goals_ antes de tentar prová-los. A ideia principal para realizar isso é notar que quando as listas de bytes de entrada têm tamanhos diferentes, então necessariamente um dos _code points_ de saída deve ser maior que o outro, visto que os intervalos delimitados pelo formato UTF-8 são disjuntos. Para isso, são provados 4 lemmas que fornecem limites inferiores e superiores para o _code point_ de saída, bem como o valor númerico um para cada tamanho da lista de entrada.

```coq
Lemma one_byte_bounds : forall byte code,
    valid_codepoint_representation [byte] ->
    utf8_dfa_decode [byte] = ([code], []) ->
    code = byte /\ 0 <= code <= 0x7f.
Proof.

Lemma two_byte_bounds : forall byte1 byte2 code,
    valid_codepoint_representation [byte1; byte2] ->
    utf8_dfa_decode [byte1; byte2] = ([code], []) ->
    code = byte1 mod 32 * 64 + byte2 mod 64
    /\ (0x80 <= code <= 0x7ff).
Proof.

Lemma three_byte_bounds : forall byte1 byte2 byte3 code,
    valid_codepoint_representation [byte1; byte2; byte3] ->
    utf8_dfa_decode [byte1; byte2; byte3] = ([code], []) ->
    code = (byte1 mod 16 * 64 + byte2 mod 64) * 64 + byte3 mod 64 /\
      (0x800 <= code <= 0xffff).
Proof.

Lemma four_byte_bounds : forall byte1 byte2 byte3 byte4 code,
    valid_codepoint_representation [byte1; byte2; byte3; byte4] ->
    utf8_dfa_decode [byte1; byte2; byte3; byte4] = ([code], []) ->
    code = ((byte1 mod 8 * 64 + byte2 mod 64) * 64 + byte3 mod 64) * 64 + byte4 mod 64 /\
      0x1000 <= code <= 0x10ffff.
```

Por fim, a prova é feita desconstruindo todos os possíveis tamanhos da lista de entrada, de 1 a 4 bytes, para ambas as as hipóteses, gerando 16 _goals_ distintos, e depois aplicando o lemma do limite específico para o tamanho da lista. A tática `lia` novamente é suficiente para provar todos os tamanhos.

```coq
Lemma utf8_dfa_increasing : decoder_strictly_increasing utf8_dfa_decode.
```

Finalmente, a prova de que `utf8_dfa_decode` segue a especificação pode ser descrita como a composição dos 5 lemmas provados anteriormente:

```coq
Theorem utf8_decoder_spec_compliant : utf8_decoder_spec utf8_dfa_decode.
Proof.
  split.
  - apply utf8_dfa_nil.
  - apply utf8_dfa_input.
  - apply utf8_dfa_output.
  - apply utf8_dfa_increasing.
  - apply utf8_dfa_projects.
Qed.
```

#pagebreak()

= Conclusão e trabalhos futuros





#pagebreak()

#bibliography("references.bib", style: "associacao-brasileira-de-normas-tecnicas")
