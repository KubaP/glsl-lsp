# OpenGL Shading Language Specification
Missing/incomplete:
- Buffer objects
- Samplers
- Images
- Atomic counters
- `f` number suffix
- `.n` float notation (skipping before dot)
- `n.` float notation (skipping after dot)
- Arrays/opaque arrays limitations
- Subroutines

# Types
### Standard Types
Scalars:
- `bool`
- `int`
- `uint`
- `float`
- `double`

Vectors (where `2 <= n <= 4`):
- `bvecn` - vector of booleans
- `ivecn` - vector of integers
- `uvecn` - vector of unsigned integers
- `vecn` - vector of floats
- `dvec` - vector of double precision floats

Matrices (where `n` is the number of columns and `m` is the number of rows, and they satisfy `2 <= n/m <= 4`):
- `matnxm` - matrix of floats
- `dmatnxm` - matrix of double precision floats

### Opaque Types
These are types which act as a reference to some external object. A clear analogy would be, like pointers are fundamentally integers but they have special meaning, the same thing is with opaque types. Opaque types can only be part of a `uniform` global variable.

- Samplers - TODO,
- Images - TODO,
- Atomic counters - TODO.

### Structs
User-defined structs can be created like so:
```glsl
struct NAME {
    float f;
    vec3 v;
};
```
Structs must have at least one member defined. Members cannot be default initialized

If a struct contains an [Opaque Type](#opaque-types), then it can only be used in places that accept such types (mainly `uniform` globals).

## Implicit Conversions
Signed integers can be implicitly converted to unsigned integers (but not the other way round).

Any integer types can be implicitly converted to a float. Integer types and floats can be implicitly converted to doubles.

Vectors and matrices can be converted if the type they're built-on can be implicitly converted.

# Identifiers
Identifiers can contain any of the following characters:
```glsl
a-z // lowercase latin
A-Z // uppercase latin
0-9 // digits
_   // underscore
```
An identifier cannot start with a digit. Identifiers starting with the `gl_` prefix are reserved for OpenGL. Identifiers also cannot be any of the keywords, reserved keywords, or built-in type identifiers.

# Literals
These are the allowed literals:
- `bool` - `true` and `false`,
- `int` - `1` (prefix `0` for base-8 or prefix `0x` for base-16),
- `uint` - `1u` or `1U` (prefix `0` for base-8 or prefix `0x` for base-16),
- `float` - `1.0` (`1e10` or `1.2e10` for exponential notation, which is always base-10),
- `double` - `1.0lf` or `1.0LF` (mixing case such as `lF` is not allowed).

Integers use *32-bit* precision. Floats are *single-precision* and doubles are *double-precision* IEEE floating point numbers.

### Numbers
For a specification of valid number notations, see the [grammar](./grammar.bnf) file.

### Operators
Mathematical operators:
```glsl
1 + 2  // Addition
1 - 2  // Subtraction
1 * 2  // Multiplication
1 / 2  // Division
1 % 2  // Remainder
1 & 2  // Bitwise AND
1 | 2  // Bitwise OR
1 ^ 2  // Bitwise XOR
1 << 2 // Binary left shit
1 >> 2 // Binary right shift

// Same as above, but assigns the result back to the variable.
// These can be either as part of an expression, or as a standalone statement.
// E.g.
//     // This will increment p by 4, and also create a copy, assigning it to i.
//     int i = p+=4; 
//
//     // This will just increment p by 4.
//     p+=4; 
i += 5
i -= 5
i *= 5
i /= 5
i %= 5
i &= 5
i |= 5
i ^= 5
i <<= 5
i >>= 5

// Same as above; can be used in expression or statement.
i++ // Increment
i-- // Decrement
~i  // Bitwise flip
```

Comparison operators:
```glsl
a == b // Equals
a != b // Not equals
a > b  // Greater than
a < b  // Less than
a >= b // Greater or equal to
a <= b // Less than or equal to

a && b // Logical AND
a || b // Logical OR
a ^^ b // Logical XOR
!a     // Logical NOT
```

|Precedence|Operator|
|-|-|
|1|`()`|
|2|`[]`, `fn_call()`, `.`, `++`, `--` (postfix)|
|3|`++`, `--` (prefix), `-` (negation; repeatable), `~`, `!` (repeatable)|
|4|`*`, `/`, `%`|
|5|`+`, `-`|
|6|`<<`, `>>`|
|7|`<`, `>`, `<=`, `>=`|
|8|`==`, `!=`|
|9|`&`|
|10|`^`|
|11|`\|`|
|12|`&&`|
|13|`^^`|
|14|`\|\|`|
|15|`?:`|
|16|`=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `^=`, `\|=`, `<<=`, `>>=`|
|17|`,` (list seperator)|

# Variables
Variables cannot be of the `void` type. This applies to any variable type, local, global, etc.

## Initialization
Variables can be initialized at the site of declaration:
```glsl
// Literal assignment
int p = 5;

// Identifier assignment, assuming 'other_float' is already declared _and_ initialized.
float f = other_float;

// Type constructor.
vec3 v = vec3(1.0, 1.0, 1.0);

// Standard function call.
mat4 m = my_func();

// Array constructor.
int i[3] = int[3](1, 2, 3);

// Initializer list.
int i[3] = {1, 2, 3};
int i[2][4] = {
    {1, 2, 3, 4},
    {5, 6, 7, 8}
};

// Struct constructor.
struct Data {
    float f;
    vec2 v;
};
Data d = Data(1.0, vec2(1.0, 2.0));
```
For `const` qualified variables (or other constant variables such as `uniform` globals), any expression must also be a *Constant Expression*.

There is technically no difference between standard function calls and type constructors.

Array constructors cannot be nested; all other initializers can.

## Global Variables
Variables in the global scope have certain special properties/abilities. There is one main distinction between global variables; they are either "standard" variables which are set/modified within the execution of the program, or they are "external" variables which either pass data *into* or *out of* the program. These variables use either the `in`, `out` or `uniform` storage qualifier.

### Standard Variables
Global variables declared without a storage qualifier (`in`, `out`, `uniform`) are just standard variables. Globals can be declared of any type or array of types; they follow the same rules as local variables:
```glsl
vec3 p;
mat4 m[2];
const float f[5][2] = {/*...*/};
```
Standard global variables can **only** have a [Const Qualifier](#qualifiers).

Standard global variables can be [Default Initialized](#initialization).

### Inputs
Inputs can be declared of any type or array of types:
```glsl
in vec3 p;
in mat4 m[2];
in VData {
    vec3 pos;
    vec3 colour;
} inData;
```
Inputs are immutable, though they are not *Constant Expressions*. Any attempt to assign to them (either directly or through `out`/`inout` qualifiers) is an error. They cannot be of a struct type, but they can be an [Interface Block](#interface-blocks) (aside from vertex inputs). They also cannot be of any [Opaque Type](#opaque-types).

Inputs into a vertex shader are also known as vertex attributes. Vertex inputs can have a [Location Qualifier](#location-qualifiers).

Fragment inputs can have a special [Fragment Test Qualifier](#fragment-test-qualifier). Fragment shaders can re-define a `gl_FragCoord` input with a [Origin Qualifier](#fragcoord-qualifier). Fragment shaders can re-define a `gl_FragDepth` input with a [Depth Qualifier](#fragdepth-qualifier).

All inputs can have a [Invariant Qualifier](#invariant-qualifier).

#### Default inputs
The following built-in inputs are present in every vertex shader:
```glsl
in int gl_VertexID;
in int gl_InstanceID;
in int gl_DrawID;       // GLSL 4.60
in int gl_BaseVertexID; // GLSL 4.60
in int gl_BaseInstance; // GLSL 4.60
```
The following built-in inputs are present in every fragment shader:
```glsl
in vec4 gl_FragCoord;
in bool gl_FrontFacing;
in vec2 gl_PointCoord;
in int gl_SampleID;
in vec2 gl_SamplePosition;
in int gl_SampleMaskIn[];
in float gl_ClipDistance[];
in int gl_PrimitiveID;
in int gl_Layer;
in int gl_ViewportIndex;
```

### Uniforms
Uniforms can be declared of any type (including [Opaque Types](#opaque-types)), array of types, or struct:
```glsl
uniform mat4 m[2];
uniform vec3 p = vec3(1.0, 0.5, 0.0);
struct Foo {
    vec2 a;
    float[5] b;
};
uniform Foo f;
```
Uniforms are immutable, though they are not *Constant Expressions*. Any attempt to assign to them (either directly or through `out`/`inout` qualifiers) is an error.

Uniforms can be [Default Initialized](#initialization) as long as they are not a [Opaque Type](#opaque-types).

Uniforms defined traditionally (not an interface block) can have a [Location Qualifier](#location-qualifiers):
```glsl
layout(location = 1) uniform vec3 p;
```
Unlike with vertex attribute location qualifiers, the index for uniforms must be unique across the entire program, i.e. using the same index in the vertex and fragment shaders **is** an error. This is an error even if the uniform declarations have the exact same identifier and type.

Uniforms can be declared as an *Interface Block*:
```glsl
uniform Foo {
    vec4 a;
    mat4 b;
} optional_name;
```
Note that *Opaque Types* are not allowed to be within a uniform interface block.

### Outputs
Outputs can be declared of any\* type or array of types:
```glsl
out vec p;
out mat4 m[2];
out VData {
    vec3 pos;
    vec3 colour;
} outData;
```
Outputs are mutable and **must** be assigned to (unless a fragment shader executes the `discard` statement). They cannot be of a struct type, but they can be an [Interface Block](#interface-blocks) (aside from fragment outputs).

Outputs cannot be of any [Opaque Type](#opaque-types). \*Outputs from the fragment shader can only be of the types: `float`, `int` and `{_, i}vecn`.

Vertex outputs can have an [Interpolation Qualifier](#interpolation-qualifiers).

Fragment outputs can have a [Location Qualifier](#location-qualifiers), an [Index Qualifier](#index-qualifier) and an [Interpolation Qualifier](#interpolation-qualifiers).

All outputs can have a [Invariant Qualifier](#invariant-qualifier).

#### Default outputs
The following built-in output is present in every vertex shader (this is not accessible in later shader stages):
```glsl
out gl_PerVertex {
    vec4 gl_Position;
    float gl_PointSize;
    float gl_ClipDistance[];
};
```
The following built-in outputs are present in every fragment shader:
```glsl
out float gl_FragDepth;
out int gl_SampleMask[];
```

### Interface Blocks
Interface blocks are defined like so:
```glsl
QUALIFIER Foo {
    vec3 p;
    mat4 m;
} OPTIONAL_NAME;
// where QUALIFIER =
uniform
in
out
buffer
```
`OPTIONAL_NAME` is the identifier of an instance of the block. If it is present, then the members within the block are effectively namespaced, i.e `OPTIONAL_NAME.m` If it isn't present, then the members are effectively global variables (and can't redefine other variables).

Blocks can also be declared as an array:
```glsl
uniform Foo {
    vec3 p;
    mat4 m;
} obj[2];
```

Interface blocks **cannot contain** [Opaque Types](#opaque-types), and types inside cannot be default initialized.

# Qualifiers
There are many qualifiers, and they must be declared in the following order:
```text
[INVARIANT] [INTERPOLATION] [LAYOUT] [PRECISION] type ...
```

For standard global variables, i.e. without any `in`/`out`/`uniform` storage qualifier, the following is valid:
```text
const type ...
```

## Invariant Qualifier
Invariant qualifiers are declared like so:
```glsl
invariant out vec3 p;

// OR

out vec3 p;
invariant p; // Makes existing declaration an invariant

// This also applies to built-in inputs/outputs, e.g.
invariant gl_Position;
```
Invariant qualifiers are entirely useless on inputs; they do not have to conform to *Interface Matching*.

## Interpolation Qualifiers
Interpolation qualifiers are declared like so:
```glsl
... out vec3 p;
// where ... =
flat
smooth
noperspective
```

## Precision Qualifiers
Precision qualifiers have no use; they are only a feature in OpenGL ES and they only exist in normal OpenGL for syntax compatibility:
```glsl
precision ...
// where ... =
highp
mediump
lowp
```
They can only be applied to `int`, `float`, `{_, i}vecn` and `matmxn` types.

## Layout Qualifiers
Layout qualifiers are annotations which precede the rest of a global variable's declaration:
```glsl
layout(...) ...
// Valid to have more than one qualifier
layout(location = 5, component = 2) ...
```

### Location
Location qualifiers are declared like so:
```glsl
location = #

// OR

location = n
//where
const n = #;
```
If there is no location qualifier for a global variable, then it is randomly assigned an index. This index is **completely arbitrary**.

### Type Sizing
Along with an index, there is a size for the location which depends on the type:

**1** index|
---|
bool
int
uint
float
{_, b, i, u}vec2
{_, b, i, u}vec3
{_, b, i, u}vec4

Matrices take up **1 per column**, so a `mat2x4` will take 2 indices. Array types take up **1 per of the above**, so a `vec2[5]` will take 5 indices, but a `mat2x4[5]` will take up 10 because each `mat2x4` is 2. The size of structs is the size of all the members in the order specified.

When an explicit location is set, all of the locations of `[n, n+size)` are taken up, so a `location = 3, size = 5` will take up indices 3 through 7, with 8 being the next free index.

When explicit location qualifiers are annotated, if they overlap, that is an error. E.g.:
```glsl
struct Foo {
    vec3 p;     // size of 1
    float[5] b; // size of 5
};
layout(location = 4) in Foo my_foo; // size of 6, the next free location is 10
layout(location = 6) in vec3 p;     // error
```
*Note:* Component qualifiers allow *some* overlap of indices; however currently unimplemented.

## FragCoord Qualifier
This is a special re-definition of the built-in `gl_FragCoord` input which defines the origin of the fragment:
```glsl
layout(...) in vec4 gl_FragCoord;
// where ... =
origin_upper_left
pixel_center_integer
// Both can be declared together.
```

## FragDepth Qualifier
This is a special re-definition of the built-in `gl_FragDepth` output which defines the depth condition:
```glsl
layout(...) out float gl_FragDepth;
// where ... =
depth_any
depth_greater
depth_less
depth_unchanged
```

## Index Qualifier
Index qualifiers are declared like so:
```glsl
index = #
```
If there is no index qualifier, then it is assigned the value 0.

## Fragment Test Qualifier
This is a special input for fragment shaders (awkward because in this example the syntax is valid even though there is no type or identifier after the `in` token):
```glsl
layout(early_fragment_tests) in;
```

# Control Flow
Control flow statements are only valid within function bodies.

### Keywords
```glsl
Valid in a function body; {EXPR} is an optional return value expression.
return {EXPR};
discard; // Valid in a function body
break;   // Only valid inside of a for loop or a switch case.
```

## If statement
```glsl
if ({EXPR}) {
    /*...*/
}

// Optionally followed by (n number of times):
else if ({EXPR}) {
    /*...*/
}

// Optionally followed by:
else {
    /*...*/
}

```
`{EXPR}` is any expression which evaluates to a `bool`.

## Switch
```glsl
switch ({EXPR}) {
    case {CONST-EXPR} : 
        /*...*/

    // Optionally followed by:
    default :
        /*...*/
}
```
`{EXPR}` is any expression.

`{CONST-EXPR}` is any constant expression.

## For Loop
```glsl
for ({VAR_DECL}; {COND_EXPR}; {INC_EXPR}) {
    /*...*/
}
```
`{VAR_DECL}` is a variable declaration (value assignment is optional).

`{COND_EXPR}` is an expression which evaluated to a `bool`.

`{INC_EXPR}` is an expression.

All 3 statements are optional, i.e. `(;;)` is a valid (infinite) loop.

# Comments
Comment syntax:
```glsl
// Comment which goes to the end-of-line

/* Comment between these delimiters */
```

Delimited comments cannot be nested, i.e. the following produces an error:
```glsl
/* First comment
    /* inner comment */ (<- First comment ends here)
*/ (<- Unmatched delimiter/punctuation)
```

Single line comments can continue with the *line-continuation character* `\`, in which case the comment extends to the EOL of the next line. So the following is one single comment:
```glsl
// First comment... \
int i = 5; // This is still part of the first comment
```

Open-ended multiline comments containing the EOF produce an error:
```glsl
// Something else

/*
<EOF>
```
Note that single-line comments, even with the `\` continuation character, can never produce this error even if they also are at the end of the file.

### Line-continuation character
```glsl
<anything but \>\<EOL>

// Valid:
keyword\
190\
ident_\
+\

// Invalid:
anything\\ // The first \ escapes the second \
```

# Preprocessor

## Directives
All preprocessor directives follow the syntax:
```glsl
#Directive ...

   #Directive ...

#    Directive ...

#Directive ... \
    Directive continues here

// This is ignored:
#
```
The `#` symbol must be the first (aside from whitespace) and the statement ends at EOL, unless a [Line-Continuation Character](#line-continuation-character) is present. The `#` can be followed by whitespace before the first directive letter.

A `#` on its own without anything after is ignored.

### Version
The version directive is specified like so:
```glsl
#version NUM PROFILE
// E.g.
#version 450 core
#version 460
```
`NUM` is the version string without the dot (`.`), so version 4.50 is `450`. Unless specified, `110` is the default.

`PROFILE` is either `core` or `compatibility`. Unless specified, `core` is the default. You can omit the profile, but the version number must be present.

This directive must be the first statement in the file (aside from whitespace/comments), and it cannot be repeated.

### Extension
The extension directive is specified like so:
```glsl
#extension NAME : BEHAVIOUR
```
`NAME` specifies the name of the extension; the value `all` is also allowed.

`BEHAVIOUR` is one of the following:
- `enable` - Enables the extension. If not supported, a warning is generated.
- `require` - Enables the extension. If not supported, the compilation fails.
- `warn` - Enables the extension. If used, it will produce warnings.
- `disable` - Disabled the extension. 

### Line
The line directive is specified like so:
```glsl
#line LINE SRC-STR-NUM
```
`LINE` must be greater than `0`. The `SRC-STR-NUM` is optional.

### C Directives
These directives come from the C language.

#### ~~include~~
```glsl
#include "FILE"
```
`FILE` is a path string.

⚠ Not supported natively by GLSL.

#### define
#### undef
```glsl
#undef SYMBOL
```
`SYMBOL` is any identifier string.

#### ifdef
```glsl
#ifdef SYMBOL
```
`SYMBOL` is any identifier string.

#### ifndef
```glsl
#ifndef SYMBOL
```
`SYMBOL` is any identifier string.

#### if
#### elif
#### else
```glsl
#else
```

#### endif
```glsl
#endif
```

#### error
Causes the compiler to error and print the text in the compile debug log output:
```glsl
#error TEXT
```
`TEXT` is any string of characters until a new line.

#### pragma
Controls compiler options:
```glsl
#pragma OPTIONS
```
`OPTIONS` is any string of characters until a new line.

## Macros
### __FILE__
It is **not** a file name. It is a decimal integer representing which string in the list of strings the shader came from.

### __LINE__
The line number

### __VERSION__
The version number as an integer, i.e. version 4.50 is `450`.

### GL_core_profile
Always defined to be `1`.

### GL_compatibility_profile
Defined to `1` if the profile is set to *compatibility*.