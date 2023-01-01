# Terminology
It can be easy to use very-similar words/phrases to describe the same things, and the same words/phrases to describe slightly different things. This document contains a list of phrases with their precise meanings to avoid ambiguity or confusion.

## Conditional compilation
|Phrase|Meaning|
|-|-|
|Conditional compilation|The process of enabling/disabling some regions of code before parsing.|
|Conditional directive|A preprocessor directive that is used for the purpose of conditional compilation.|
|Controlling conditional directive|A preprocessor directive which controls the inclusion of a conditional branch, e.g. `#ifdef` or `#else`. **This excludes `#endif`.**|
|Conditional block|A group of conditional branches/directives. A block starts with a `#if`/`#ifdef`/`#ifndef` and ends with a `#endif` directive.|
|Conditional branch|A region of code that may or may not be included depending on the controlling conditional directive before it. It spans from the controlling conditional directive before it to the next conditional directive, be it an `#elif`/`#else` or an `#endif`. A branch is part of a conditional block.|
|Key|A key describes a set of conditional branches. It is ordered chronologically based on the order of appearance of the controlling conditional directives in the source file. It can select as many or as few branches as desired, but two branches from the same block cannot be selected.|
|Conditional compilation is disabled|Conditional compilation is disabled, so no conditional branches are included.|
|Conditional compilation is evaluated|Conditional compilation is enabled and follows the normal evaluation rules as described in the specification.|
|Conditional compilation is enabled using a key|Conditional compilation is enabled, but rather than following the normal evaluation rules, conditional branches are included only if they are part of the key.|

## Macro expansion
|Phrase|Meaning|
|-|-|
|Macro|A bit of text that is replaced with some other text.|
|Macro expansion|The process of (recursively) replacing a macro call site with the replacement list of that macro.|
|Macro call site|The actual invocation of a macro.|
|Macro definition|The `#define` directive and all of its contents.|
|Macro's name|The identifier of a macro.|
|Macro's signature|The identifier and optional parameter list that defines a macro.|
|Macro's replacement list|The list of tokens that replace the macro call site.|
|Object-like macro|A macro which just expands to some content.|
|Function-like macro|A macro which takes zero or more parameters and expands to some content, potentially including the parameters in the output.|

## Extension
|Phrase|Meaning|
|-|-|
|Configuration|A collection of settings that comprise a logical unit of configuration.|
|Setting|A key-value pair that controls something.|

## Parser
|Phrase|Meaning|
|-|-|
|Source string|The input into the lexer (or entire parser pipeline).|
|Lexer|The transformation from the source string into a token stream.|
|Token stream|The vector of tokens. This is produced by the lexer.|
|Parser|The transformation of the token stream into an AST. The first part transforms a token stream into a token tree, and the second part transforms a token tree into an AST.|
|Token tree|A tree layout of token streams. This is produced from first part of the parser.|
|AST|An abstract syntax tree representing the relevant parts of a source string. This is produced from the second part of the parser.|