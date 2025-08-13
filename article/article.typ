#import "template.typ": project

#show: project.with(
    title: "Verificação formal de uma implementação eficiente de UTF-8",
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



= Trabalhos relacionados
