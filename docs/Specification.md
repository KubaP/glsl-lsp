# OpenGL Shading Language Specification
This is a document outlining the GLSL 4.50 specification. It is effectively a rewrite of the official specification pdf in order to a) order the information in a more cohesive manner, b) provide intra-doc links, c) make it easier to read through a less terse language.

Missing/incomplete:
- Buffer objects
- Samplers
- Images
- Atomic counters
- Arrays/opaque arrays limitations

# Character Set
GLSL source strings **must** use the UTF-8 encoding. Only the following characters are allowed in GLSL tokens (preprocessor tokens can accept any character):
- `[a-z]`, `[A-Z]`, `_`,
- `[0-9]`,
- `+`, `-`, `*`, `/`, `%`, `<`, `>`, `&`, `|`, `^`, `~`, `=`, `!`, `?`, `:`, `(`, `)`, `[`, `]`, `{`, `}`, `;`, `,`, `.`

Any other characters produce a compile-time error.

There are no digraphs or trigraphs, and no escape sequences other than the [line-continuation character](#line-continuation-character).

The following are reserved keywords, using any of these results in a compile-time error:
```glsl
common partition active
asm
class union enum typedef template this
resource
goto
inline noinline public static extern external interface
long short half fixed unsigned superp
input output
hvec2 hvec3 hvec4 fvec2 fvec3 fvec4
sampler3DRect
filter
sizeof cast
namespace using
```

# Types
Note that the term *composites* refers to any of the vector, matrix, array or struct types.

Unlike in C, there are no pointer types.

### Standard Types
Scalars:
- `bool` - Genuine boolean which can hold one of two values; not an integer like in C.
- `int` - Signed 32-bit integer.
- `uint` - Unsigned 32-bit integer.
- `float` - Single precision floating point number.
- `double` - Double precision floating point number.
- `void` - Nothing.

`void` is a special type which can only be used in function signatures to denote a function not returning anything. It cannot be used to declare a variable which stores some data.

Vectors (where `2 <= n <= 4`):
- `bvecn` - Booleans.
- `ivecn` - Integers.
- `uvecn` - Unsigned integers.
- `vecn` - Single precision floats.
- `dvec` - Double precision floats.

Matrices (where `n` is the number of columns and `m` is the number of rows, and they satisfy `2 <= n/m <= 4`):
- `matnxm` - Single precision floats.
- `dmatnxm` - Double precision floats.

An alternative `mati` and `dmati` notation, (where `i` is a number that satisfies `2 <= i <= 4`), defines a square matrix. It is equivalent to `(d)matixi`.

### Opaque Types
These are types which act as a reference to some external object. A clear analogy would be, like pointers are fundamentally integers but they have special meaning, opaque types are also integer primitives but they point to somewhere else in gpu memory. Opaque types can only be declared as `uniform`-qualified variables, or as function parameters.

Opaque types are a form of constant variables; they cannot be assigned to, and hence cannot be qualified with the `out` or `inout` parameter qualifiers.

- TODO: Samplers
- TODO: Images
- TODO: Atomic counters

### Structs
User-defined structs can be created like so:
```glsl
struct NAME {
    float f;
    vec3 v;
};
```
Structs must have at least one member defined. Members cannot be initialized. Note the semi-colon (`;`) at the end; this is necessary.

If a struct contains an [Opaque Type](#opaque-types), then it can only be used in places that accept such types (mainly `uniform` globals).

Struct members are defined using standard [Variable Definition](#variable-definitions--initializations) statements, i.e. all of the following are valid:
```glsl
struct NAME {
    int[3] a;
    bool b[3];
    float[1] c[5];
    vec2 one, two;
    mat4[2] m1[1], m2;
};
```
Unlike with variable definitions, array members **must** be sized. Anonymous members are not allowed. Embedded struct definitions are also not allowed.

## Arrays
Any type (other than `void`) can be aggregated into an array of homogenous values:
```glsl
// Sized:
float f[3]

// Unsized:
mat4 m[]

// Size specified by a more complex constant expression:
const int size = 2;
vec3 v[size + 5]
```
If an array size is specified, it must be a *Constant Expression* which evaluates to a greater-than-zero integer.

Multi-dimensional arrays can also be typed:
```glsl
// 3 sets of arrays, each 5 in length:
float f[3][5]

// Equivalent to above:
float[5] f[3]

// A 3d array:
mat4 m[2][3][9]

// Equivalent to above:
mat4[3][9] m[2]

mat4[9] m[2][3]
```

## Initialization
All types can be initialized with an initialization expression. This expression must evaluate either to that type, or to a type which can be implicitly converted to that type.

### Scalar
Scalars can be initialized through the following:
```glsl
// An expression consiting of a literal:
int i = 5;

// A simple binary expression:
int i = 5 + 10;

// A more complex nested binary expresion:
int i = (5 + 7) << 9;

// An expression consiting of a function call which returns a value:
int i = func();
```
You can combine the different expression types above in any arbitrary way.

Scalars can also be explicitly created using constructors, if the type provided can be converted:
```glsl
TODO:
```

### Vectors and Matrices
Vectors and matrices can be initialized through constructors:
```glsl
// Initialises a vec3 with the given values:
vec3 v = vec3(1.0, 2.0, 3.0);

// Initialises a vec3 with all zeroes:
vec3 v = vec3(0.0);

// Initialises a mat2x2 with the given values:
mat2 m = mat2(1.0, 2.0, 10.0, 20.0);
mat2 m = mat2(vec2(1.0, 2.0), vec2(10.0, 20.0));
```
The number of arguments in a constructor must match one of the constructor overloads. Depending on which overload is chosen, each expression must evaluate to the parameter type, or a type which can be implicitly converted to the parameter type.

Alternatively, initializer lists can be used:
```glsl
vec3 v = {1.0, 2.0, 3.0};

mat2 m = {{1.0, 2.0}, {10.0, 20.0}};
```
Each expression in an initializer list must either evaluate to the constituent type of the vector/matrix, or a type which can be implicitly converted to the constituent type.

Initializer lists must contain the same amount of expressions as the number of components in the vector. The following is not allowed:
```glsl
// Valid:
vec3 v = vec3(0.0);

// Invalid:
vec3 v = {0.0};

// Valid:
vec3 v = {0.0, 0.0, 0.0}; // x, y, z
```
Initializer lists must contain the same amount of expressions as the number of columns in the matrix. Matrices are "under the hood" treated as a bunch of vectors, one vector per column, hence the following happens:
```glsl
// Valid:
mat2 m = mat2(1.0, 2.0, 3.0, 4.0);

// Invalid:
mat2 m = {1.0, 2.0, 3.0, 4.0};

// This _is_ allowed however:
// See how you're effectively first initializing two `vec2`s, and then using those to initialize the `mat2`
mat2 m = {{1.0, 2.0}, {3.0, 4.0}};
// It is the equivalent of:
mat2 m = mat2(vec2(1.0, 2.0), vec2(3.0, 4.0));
```

### Arrays
Arrays can be initialized through constructors:
```glsl
// Initialize 3 elements:
int i[3] = int[3](1, 2, 3);

// You don't have to repeat the size:
int i[3] = int[](1, 2, 3);

// You can skip out the size entirely if you are initializing in one go:
int i[] = int[](1, 2, 3);

// Alternatively, the size can go on the type:
int[3] i = int[](1, 2, 3);
int[] i = int[](1, 2, 3);

// Invalid, incorrect number of arguments:
int i[3] = int[](1, 2);
```
The number of arguments in a constructor must match the size of the array (if explicitly specified). Each expression must evaluate to the element type, or a type which can be implicitly converted to the element type. If no explicit size is specified, the number of arguments can be arbitrary.

Multi-dimensional arrays cannot be initialized with nested array constructors:
```glsl
// Invalid:
int i[2][3] = int[2](
    int[3](1, 2, 3),
    int[3](4, 5, 6)
);

// Use initializer lists instead:
int i[2][3] = {{1, 2, 3}, {4, 5, 6}};
int i[2][3][1] = {{{1}, {2}, {3}}, {{4}, {5}, {6}}};

// Or alternatively construct it in multiple steps:
int a[] = int[](1, 2, 3);
int b[] = int[](4, 5, 6);
int i[2][3] = int[](a, b);

// Or alternatively use only inner constructors:
int i[2][3] = {int[](1, 2, 3), int[](4, 5, 6)};

// Alternatively, put the inner dimension size first:
int[3] i[2] = {int[](1, 2, 3), int[](4, 5, 6)};
int[1] i[2][3] = {{{1}, {2}, {3}}, {{4}, {5}, {6}}};

// Invalid, only the inner-most size can be moved forward:
int[1][3] i[2] = {{{1}, {2}, {3}}, {{4}, {5}, {6}}};
```
With multi-dimensional arrays, only the outer-most size can be implicit:
```glsl
// Valid, automatically infers: int[2][3]:
int i[][3] = {{1, 2, 3}, {4, 5, 6}};
int[3] i[] = {{1, 2, 3}, {4, 5, 6}};

// Invalid:
int i[][] = {int[3](1, 2, 3), int[3](4, 5, 6)};

// Also invalid, inner size not specified:
int[] i[2] = {{1, 2, 3}, {4, 5, 6}};
int[] i[2][3] = {{{1}, {2}, {3}}, {{4}, {5}, {6}}};
```

Alternatively, initializer lists can be used:
```glsl
// Explicit size:
int i[3] = {1, 2, 3};

// Implicit size:
int i[] = {1, 2, 3};

int i[3][2] = {{1, 2}, {3, 4}, {5, 6}};

int i[2][3][1] = {{{1}, {2}, {3}}, {{4}, {5}, {6}}};
```
Each expression in an initializer list must be either evaluate to the element type, or a type which can be implicitly converted to the element type.

Initializer lists must contain the same amount of expressions as the number of elements in the array. The following is not allowed:
```glsl
// Invalid:
// Provided only 2 expressions, but there are 3 elements in the array
int i[3] = {0, 1};

// Provided 4 expressions, but there are only 3 elements
int i[3] = {0, 1, 2, 3};
```

### Structs
Structs can be initialized through a constructor:
```glsl
struct Data {
    int i;
    float f;
    mat2 m;
};

// Initializes the struct:
Data d = Data(5, 1.0, mat2(0.0));

// Invalid:
Data d = Data(5, 1.0);
```
The order of the arguments corresponds to the order the struct members are declared in. The number of arguments must match the number of members of the struct.

Alternatively, initializer lists can be used:
```glsl
Data d = {5, 1.0, mat2({0.0, 0.0}, {0.0, 0.0})};
```
Each expression in an initializer list must be either evaluate to the type of the relevant member, or a type which can be implicitly converted to the relevant member. The following would not be allowed for example:
```glsl
// The second argument should be of `float`, but it is of `mat2`
// The second and third arguments should be swapped around
Data d = {5, mat2(0.0), 1.0};
```

Initializer lists must contain the same amount of expressions as the number of members in the struct. The following is not allowed:
```glsl
// Provided only 2 expressions, but there are 3 members in the struct
Data d = {5, 1.0};

// Provided 4 expressions, but there are only 3 members
Data d = {5, 1.0, mat2(0.0), 7};
```

### Opaque Types
Opaque types do not support initialization at all; any attempt to do so is illegal.

### Note about Initializer Lists
Child initializer lists can only be used if the parent composite-type also uses an initializer list:
```glsl
struct Data {
    int i;
    mat2 m;
};

// Valid:
// Only uses initializer lists
Data d = {
    1,
    {{1.0, 2.0}, {3.0, 4.0}}
};

// Valid:
// Uses the initializer list for the top-most composite,
// but constructors for the nested `mat2` and `vec2` composites.
Data d = {
    1,
    mat2(vec2(1.0, 2.0), vec2(3.0, 4.0))
};

// Invalid:
// Uses an initializer lists for the top-most composite,
// a constructor for the nested `mat2` composite,
// and then an initializer list for the nested `vec2` composites.
Data d = {
    1,
    mat2({1.0, 2.0}, {3.0, 4.0});
};
// See how the `vec2` initializer lists are within a normal constructor. This is not allowed.

// More invalid examples:
Data d[2] = {
    Data(1, {{1.0, 2.0}, {3.0, 4.0}}),
    Data(1, {{1.0, 2.0}, {3.0, 4.0}}),
};
Data d[2] = {
    {1, mat2({1.0, 2.0}, {3.0, 4.0})},
    {1, mat2({1.0, 2.0}, {3.0, 4.0})},
};

mat2 m = mat2({1.0, 2.0}, {3.0, 4.0});

int i[2][3] = int[2]({1, 2, 3}, {4, 5, 6});
```
Initializer Lists can have a trailing comma after the arguments, i.e. this is valid:
```glsl
// Valid:
vec2 v = {1, 2,};

// Also valid:
vec2 v = {1, 2};

// This however is invalid:
vec3 v = {1, 2, ,};
//             ^ expected argument between the two commas
```
Note that this is **unlike** function calls, where a trailing comma is invalid.

## Implicit Conversions
The following implicit conversions are available:

| From                     | To        |
| ------------------------ | --------- |
| `int`                    | `uint`    |
| `int`, `uint`            | `float`   |
| `int`, `uint`, `float`   | `double`  |
| `ivecx`                  | `uvecx`   |
| `ivecx`, `uvecx`         | `vecx`    |
| `ivecx`, `uvecx`, `vecx` | `dvecx`   |
| `matnxm`                 | `dmatnxm` |
| `mati`                   | `dmati`   |

Arrays do not have any implicit conversions, even if the the element type does have conversions.

Structs do not have any implicit conversions, even if both structs have the exact same member layout.

# Identifiers
Identifiers can contain any of the following characters:
```glsl
a-z // lowercase latin
A-Z // uppercase latin
0-9 // digits
_   // underscore
```
An identifier cannot start with a digit. Identifiers starting with the `gl_` prefix are reserved for OpenGL. Identifiers starting with a `__` prefix are by convention reserved; they can be (un)defined but it may cause unintended behaviour if a previous implementation definition exists. Identifiers also cannot be any of the keywords or reserved keywords.

# Literals
These are the allowed literals:
- `bool` - `true` and `false`.
- `int` - `1`, (prefix `0` for base-8 or prefix `0x` for base-16).
- `uint` - `1u` or `1U`, (prefix `0` for base-8 or prefix `0x` for base-16).
- `float` - `1.0`, (`1e10` or `1.2e10` for exponential notation, which is always base-10).
- `double` - `1.0lf` or `1.0LF`, (mixing case such as `lF` is not allowed).

### Numbers
For a specification of valid number notations, see the [lexer_grammar.bnf](./lexer_grammar.bnf) file.

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

| Precedence | Operator                                                                |
| ---------- | ----------------------------------------------------------------------- |
| 1          | `()` (bracket grouping)                                                 |
| 2          | `[]` (index), `fn_call()`, `.` (object access), `++`, `--` (postfix)    |
| 3          | `++`, `--` (prefix), `-` (negation), `~` (repeatable), `!` (repeatable) |
| 4          | `*`, `/`, `%`                                                           |
| 5          | `+`, `-`                                                                |
| 6          | `<<`, `>>`                                                              |
| 7          | `<`, `>`, `<=`, `>=`                                                    |
| 8          | `==`, `!=`                                                              |
| 9          | `&`                                                                     |
| 10         | `^`                                                                     |
| 11         | `\|`                                                                    |
| 12         | `&&`                                                                    |
| 13         | `^^`                                                                    |
| 14         | `\|\|`                                                                  |
| 15         | `?:` (ternary)                                                          |
| 16         | `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `^=`, `\|=`, `<<=`, `>>=`      |
| 17         | `,` (list seperator)                                                    |

Only the `.` object access, `==`, `!=` and `=` operators are allowed to operate on [Structs](#structs).

Only the `==`, `!=`, `=` and `[]` index operators are allowed to operate on [Arrays](#arrays). The `.` object access is allowed to access the `length()` method only.

# Statements & Expressions

## Variable Definitions & Initializations
Variable definition (& initialization) statements are valid at the top-level of a shader file, and within functions or any other control flow statements or blocks. Variables can be defined of any type (other than `void`):
```glsl
// A definition:
int i;

// A definition with initialization:
int i = 5;
```

### Initialization
See the [Initialization](#initialization) section for an overview of how different types can be initialized.

If a variable is not initialized at the site of definition, it must be later initialized before it can be used:
```glsl
// Defined but not initialized:
float b[3];

// Initialized:
b = float[](1, 2, 3);
```
For `const` qualified variables (or other constant variables such as `uniform` globals), any assignment expression must also be a *Constant Expression*.

### Multiple At Once
In a variable definition (& initialization), multiple variables can be created in one statement:
```glsl
int a, b;

int a, b = 5;

// Defines `a` of `int[3][1]` and `b` of `int[5][1]`:
int[1] a[3], b[5];
```
If more than one variable is defined of a different array size, the statement cannot initializer the variables (because there would be a type mismatch):
```glsl
// One array has an outer size of 3 but the other of 5:
int[1] a[3], b[5] = int[](/*???*/);
```

## Variable Assignment
Variable assignment statements are valid at the top-level of a shader file, and within functions or any other control flow statements or blocks:
```glsl
// Assuming int p; :
p = 5;

// Assuming float b[2][4]; :
b = {
    {1, 2, 3, 4},
    {5, 6, 7, 8}
};
```
Variable assignment can also take a shorthand form if the expression involves the variable:
```glsl
p += 1;

// The same as:
p = p + 1;
```

Variables can be assigned to within an expression like so:
```glsl
// This will increment `p` by 4, and assign a copy of this new value to `i`:
int i = p += 4;
```

## Function Definitions & Declarations
Function declaration & definition statements are only valid at the top-level of a shader file, i.e. they cannot be nested in any way. There is a distinction between a declaration and a definition:
> A declaration declares the signature of a function (akin to a prototype), whilst a definition does that plus it also defines the behaviour of said function.

A definition can exist in its own, however a declaration must also have a definition at some point for the function to be valid:
```glsl
// A declaration:
int func(int i);

// A definition:
int func(int i) {
    // Do something
    return 5;
}
```
Within a function definition, the return type must match, or be able to be implicitly converted to, the return type specified in the function definition. If the return type is of `void`, the `return;` control flow statement must be used without any returning expression.

Functions are allowed to return any type, and take in any type other than `void` for the parameter types. Arrays are allowed, but they must be explicitly sized:
```glsl
// A function with no parameters:
void func();

// A function with multiple parameters:
mat4 func(int i, float f, mat4 m);

// Invalid, `void` cannot be a parameter:
void func(void v);

// A function with arrays:
vec3[3] func(int[2] i);

// Just like with variable definitions, array sizes can be disjointed:
vec3[3] func(int[2] i);
vec3[3] func(int[2] i[1]);

// Invalid, arrays must be sized:
vec3[] func(int[2] i);
```

The parameter names are optional in both the declaration and definition, so the following is allowed:
```glsl
void func(int i, float, mat4 m);
```

A function that takes no parameters can have an optional `void` parameter specified. If this is the case, it must be the only parameter, and it must be anonymous:
```glsl
int func(void);

// Equivalent to:
int func();

// The following are all invalid:
int func(void, void);
int func(void, int);
int func(void v);
```

### Qualifiers
#### Passing
There are multiple ways that arguments are passed into a function:
- `in` - The argument value is copied into the function,
- `out` - The parameter value within the function is copied out into this argument,
- `inout` - The argument value is copied into the function, and then the parameter value within the function is copied back out into the same argument.

The default behaviour is of `in`.
```glsl
void func(in int i);

void func(out int i);

void func(inout int i);
```
#### Const
Parameters can be constant qualified:
```glsl
// Valid, implicit `in`
void func(const int i);

// Valid, explicit `in`
void func(const in int i);

// Invalid
void func(const out int i);
void func(const inout int i);
```
The `const` qualifier can only be used with the `in` passing qualifier.

#### Precision
The precision of the return type can be specified with a [precision qualifier](#precision-qualifiers):
```glsl
PRECISION float func();
```

## Function Calls
Function call statements/expressions are only valid within function bodies:
```glsl
// A statement:
func();

// Part of an expression:
... = vec3(0.0); // <- Returns a value

// Functions can have an arbitrary number of arguments:
func(1, 5.0, Data(1));
```

There are multiple ways that arguments are passed into a function call:
- `in` - The argument value is copied into the function.
- `out` - The parameter value within the function is copied out into this argument.
- `inout` - The argument value is copied into the function, and then the parameter value within the function is copied back out into the same argument.

```glsl
// Standard passing of arguments in:
fn(in int p) {
    // Reads from `p` and does something...
}
int i = 5;
fn(i);

// Passing parameters out:
fn2(out int p) {
    p = 5;
}
int i;
fn2(i);
// `i` is now 5

// Both:
fn3(inout int p) {
    p += p;
}
int i = 5;
fn3(i);
// `i` is now 10
```

Note that an argument is expected after a comma, i.e. this is invalid:
```glsl
// Invalid:
vec2(1, 2, )
//        ^ expected argument here

// Valid:
vec2(1, 2)
```

## Subroutines
Subroutines are special functions which can have one or more variants, one of which is selected at runtime through a uniform. You first declare a subroutine type which provides a function declaration only. Then you define one or more functions which are associated with that subroutine and match the signature. Finally you define a special uniform which acts as a function that you can call in normal code.

### Subroutine Type
A subroutine type is declared in the same manner as a function:
```glsl
subroutine int func(int i);
```
In this example `func` is the typename of the subroutine.

### Function Association
Function definitions are associated with a certain subroutine type through the extra syntax:
```glsl
// Associated with the subroutine `func`:
subroutine(func) int func_1(int i) {
    // Do something
    return 5;
}

// Associated with multiple subroutines:
subroutine(func, foobar) int baz(int i) {
    // Do something
    return 5;
}
```
The arguments and return type must match the subroutine type, (if multiple subroutines are associated they all must have the same arguments and return type). The name of a function doesn't have to match, but it must be unique if it is associated with a subroutine. The following would be invalid:`
```glsl
subroutine(func) int func_1(int i) {
    return 5;
}

// This isn't a subroutine function, but the names clash nontheless:
int func_1(int i, int p);
```
Function declarations cannot be associated; a body is necessary. Associated functions can also be called directly through their function name.

### Subroutine Uniform
A subroutine uniform is defined:
```glsl
subroutine uniform func my_func;

// Can also be defined as an array:
subroutine uniform func my_func[2];
```

### Calling
A subroutine is called within normal code by calling the name of the subroutine uniform like so:
```glsl
int i = my_func(0);

// Also works with arrays:
int i = my_func[1](0);
```
This will call the currently chosen subroutine function, whatever it may be. Control over which subroutine function is chosen is done through the OpenGL API which is irrelevant to this specification.

### Layout specification
Individual subroutine function definitions as well as the subroutine uniform can have their in-shader layout specified:
```glsl
layout(index = 2) subroutine(func) int func_1(int i) { return 5; }

layout(index = 5) subroutine uniform func my_func;
```

## Control Flow
Control flow statements are only valid within function bodies.

### Jumps
```glsl
// Only valid inside for, while and do-while loops:
continue;

// Only valid inside for, while and do-while loops, as well as switch statements:
break;

// Valid inside any function:
return;
return _EXPR_;

// Only valid in fragment shaders, inside any function:
discard;
```
`_EXPR_` is an expression.

Unlike in C, there is no `goto` statement.

### If Statement
```glsl
if (_EXPR_) {
    /*...*/
}

// Optionally followed by (n number of times):
else if (_EXPR_) {
    /*...*/
}

// Optionally followed by:
else {
    /*...*/
}

```
`_EXPR_` is an expression which evaluates to a `bool`.

If the body only contains one statement, the braces can be omitted. If the braces are omitted, there **must** be one statement after; a lack of statement produces a compile-time error:
```glsl
if (_EXPR_)
    /*...*/
else if (_EXPR_) // <- error
else
    /*...*/

// We can mix and match:
if (_EXPR_) {
    /*...*/
} else if (_EXPR_)
    /*...*/
else {
    /*...*/
}
```

### Switch
```glsl
switch (_EXPR_) {
    // Optionally repeated (n number of times):
    case _CONST-EXPR_ : 
        /*...*/

    // Optionally followed by:
    default :
        /*...*/
}
```
`_EXPR_` is an expression which evaluates to either `int` or `uint`.

`_CONST-EXPR_` is a constant expression which evaluates to either `int` or `uint`.

If there is a difference in type between `_EXPR_` and `_CONST-EXPR_`, then an implicit conversion will take place from `int` to `uint`.

### For Loop
```glsl
for (_INIT-STMT_; _COND-EXPR_; _LOOP-EXPR_) {
    /*...*/
}
```
`_INIT-STMT_` is a either a statement or an expression. It is evaluated once at the start of the loop. It can be a variable definition.

`_COND-EXPR_` is an expression which evaluated to a `bool`.

`_LOOP-EXPR_` is an expression.

All 3 parts are optional, i.e. `for (;;)` is a valid (infinite) loop.

### While Loop
```glsl
while (_COND-EXPR_) {
    /*...*/
}
```
`_COND-EXPR_` is an expression which evaluates to `bool`.

### Do-While Loop
```glsl
do {
    /*...*/
} while (_COND-EXPR_);
```
`_COND-EXPR_` is an expression which evaluates to `bool`.


# Variables
Variables can be of any type (other than `void`).

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

## Const Qualifier
The const qualifier is:
```glsl
const
```
This makes the variable read-only; it cannot be written to.

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
Interpolation qualifiers are one of the following:
```glsl
flat
smooth
noperspective
```
- `flat` - The value will not be interpolated. It will have the same value for every fragment within a triangle.
- `smooth` - The value will be interpolated in a perspective-correct manner over the primitive being rendered.
- `noperspective` - The value will be interpolated in a linear screen-space manner.

## Precision Qualifiers
Precision qualifiers have no use; they are only a feature in OpenGL ES and exist in standard OpenGL for syntax compatibility:
```glsl
highp
mediump
lowp
```
They can only be applied to `int`, `float`, `{_, i}vecn` and `matmxn` types.

## Layout Qualifiers
Layout qualifiers are declared like so:
```glsl
// With an identifier:
layout(depth_any)

// Or with an identifier-value pair:
layout(location = 1)
```
Layout qualifiers can take one or more identifiers in the form of a list. A given identifier can also be re-declared within the list (and if that is the case, only the last occurrence of the identifier is applied).
```glsl
layout(location = 0)

layout(location = 2, component = 5)

// `location = 0` is effectively ignored
layout(location = 0, index = 1, location = 6)
```

### Location
Location qualifiers are declared like so:
```glsl
location = EXPR
```
`EXPR` is a *Constant Expression* which evaluates to a positive integer.

<!-- If there is no location qualifier for a global variable, then it is randomly assigned an index. This index is **completely arbitrary**. -->

### Component
Component qualifiers are declared like so:
```glsl
component = EXPR
```
`EXPR` is a *Constant Expression* which evaluates to a positive integer.

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

# Line-Continuation Character
The line-continuation character makes the lexer ignore itself and the end-of-line characters that follow, and continue lexing from the first character of the next line **as if there was no break**:
```glsl
<ANYTHING>\<EOL>
```
`<ANYTHING>` is anything other than `\`. `<EOL>` is either `\n` or `\r\n`. Two slashes (`\\`) produce a compile-time error:
```glsl
i +\
= 5;
// Would be lexed as:
i += 5;

i +\\
= 5;
// Would be lexed as:
i +<ERROR>=5;
```
Note that this allows keywords and identifiers to be split in half:
```glsl
str\
uct I;

// Would be lexed as:
struct I;

str\
    uct I;

// Would be lexed as:
str uct I;
// because preceding whitespace on the next line is not removed
```

# Comments
Comment syntax:
```glsl
// Comment which goes to the end-of-line

/* Comment between these delimiters */
```

Delimited comments cannot be nested, i.e. the following produces a compile-time error about an unexpected punctuation symbol:
```glsl
/* First comment
    /* inner comment */ (<- First comment ends here)
*/ (<- Unmatched delimiter/punctuation)
```

Single line comments can continue with the [Line-Continuation Character](#line-continuation-character) `\`, in which case the comment extends to the end-of-line of the next line. So the following is one single comment:
```glsl
// First comment... \
* int i = 5; This is still part of the first comment *
```

Open-ended block comments containing the end-of-file produce a compile-time error:
```glsl
// Something else

/*
<EOF>
```
Note that single-line comments, even with the `\` line-continuation character, can never produce this error even if they also are at the end of the file.

# Preprocessor
The preprocessor is a single-pass scan. This means that, for example, a macro cannot create a new directive.

The GLSL preprocessor is based off the C++98 standard: [ISO/IEC 14882:1998](https://www.lirmm.fr/~ducour/Doc-objets/ISO+IEC+14882-1998.pdf), but it:
- Has no support for digraphs or trigraphs.
- Has no support for string or character literals, and hence no support for the stringizing operator.
- Has no support for universal character names (`\uXXXX` notation).
- Has no support for any number literals other than integers (with no prefixes/suffixes).
- Has the extra [version](#version) and [extension](#extension) directives, and lacks the [include](#include) directive.
- Has a different [line](#line) directive, since GLSL has no concept of filenames.
- Has different pre-defined macros, (which depend on the exact GLSL version).

## Token Concatenation Operator (##)
The token concatenation operator (sometimes referred to as the pasting operator) joins two tokens, removing any whitespace in the process:
```glsl
#define TEST 4##9

// Spaces between the tokens and the operator are allowed:
#define TEST 4 ## 9
```
Any use of `TEST` would expand to the number token `49`.

This operator can only be used within the replacement-list of a [define](#define) directive; everywhere else it is treated as two individual `#` characters, (which may or may not be legal depending on the specific directive). A compile-time error is produced if there is no token before/after the operator. A compile-time error is produced if a `##` is located immediately after the operator, i.e. `####`. An attempt to combine two tokens which cannot be compined (e.g. `500##+`) results in no combination; the two tokens remain as separate. A warning may be produced in such a case.

The main use of this operator is to concatenate an argument in a function-like macro with hardcoded tokens:
```glsl
#define TRAILING_2(a) a##00

int i = TRAILING_2(5); // Expands to: int i = 500;
```
It is possible to chain the operator like so:
```glsl
#define DOT(a, b) a##.##b

int i = DOT(5, 0); // Expands to: int i = 5.0;
```

## Directives
All preprocessor directives follow the syntax:
```glsl
#_DIRECTIVE_ _CONTENTS_

// All valid:
#Directive ...

   #Directive ...

#    Directive ...

#Directive ... \
    Directive continues here

/* foo */ # Directive ...

#
```
`_DIRECTIVE_` is a name of an accepted directive. A name that is not accepted produces a compile-time error.

`_CONTENTS_` is a list of tokens for the directive; which preprocessing tokens are and aren't allowed depends on the directive.

The `#` symbol must be the first (aside from whitespace or comments) token on the new line and the statement ends at the end-of-line (taking into account any [Line-Continuation Characters](#line-continuation-character)). The `#` can be followed by whitespace before the directive name.

A `#` on its own without anything afterwards until the end-of-line is completely ignored.

## Version
The version directive is specified like so:
```glsl
#version _NUM_
#version _NUM_ _PROFILE_

// Examples:
#version 460
#version 450 core
#version 310 es
```
`_NUM_` is the GLSL version number as an integer without the dot (`.`), so version 4.50 is `450`; only valid GLSL version numbers are accepted, any other value produces a compile-time error. It is mandatory. The default behaviour assumes `110`.

`_PROFILE_` is either `core`, `compatibility` or `es`; any other value produces a compile-time error. It is optional, unless version is `300` or `310` in which case the profile must be `es`. It can only be used if the version number is `150` or greater. The default behaviour assumes `core`. 

This directive, if present at all, must be the first statement in the file (aside from whitespace or comments), and it cannot be repeated.

## Extension
The extension directive is specified like so:
```glsl
#extension _NAME_ : _BEHAVIOUR_
#extension all : _BEHAVIOUR_

// Examples:
#extension ARB_vertex_buffer_object : enable
#extension all : warn
```
`_NAME_` specifies the name of the extension. It is mandatory. It can be substituted with the string `all`.

`_BEHAVIOUR_` is mandatory, and one of the following:
- `require` - Enables the extension. If not supported, it produces a compile-time error.
- `enable` - Enables the extension. If not supported, a warning is generated.
- `warn` - Enables the extension. If used, it will produce warnings. If not supported, a warning is generated.
- `disable` - Disabled the extension. If used, it produces a compile-time error.
- 

If `all` is used for `_NAME_`, the following behaviour is exhibited:
```glsl
// Produce warnings any time any extension is used:
#extension all : warn

// Produce errors any time any extension is used:
// (This is the default state of the compiler)
#extension all : disable

// The following are invalid and result in an error:
#extension all : require
#extension all : enable
```
The order of extension directives matters; configuring an extension overwrites any previous configurations of that extension.

## Line
The line directive is specified like so:
```glsl
#line _LINE_ _SRC-STR-NUM_

// Examples:
#line 10
```
`_LINE_` is a number greater than `0`. 

`_SRC-STR-NUM_` is a number greater than `0`. It is optional.

⚠ This is the only directive within which macros are expanded, though nested expansions are not supported. The following is valid:
```glsl
#define FOO 5

// Expands to: #line 5
#line FOO
```
But this wouldn't be:
```glsl
#define FOO 5
#define BAR FOO

#line BAR
```

After processing this directive, the compiler will behave as if it compiling at line number `LINE` and source string number `SRC-STR-NUM`. Subsequent lines will be numbered sequentially, until another `#line` directive overrides this.

## ~~include~~
⚠ Not supported natively by GLSL.
```glsl
#include _FILE_
```

## define
Defines a macro, which is textually substituted at any call site.

### Object-like
An object-like macro is one which is simply substituted by replacement tokens:
```glsl
#define _NAME_ _REPLACEMENT-LIST_

// Examples:
#define TOGGLE
#define INC ++
#define RETURN if (true) return;
```
`_NAME_` is the name of the macro. It is mandatory.

`_REPLACEMENT-LIST_` is a list of tokens which will replace any invocation of this macro. It is optional. It can contain any GLSL tokens in any order (mismatched braces, invalid tokens, etc.), but if the macro is expanded the tokens will be checked for validity as normal. If this list is empty, invoking the macro will replace it with an empty string, i.e. remove it.

Token concatenation happens first, then any nested macros are expanded. Token concatenation operators are effectively unnecessary within an object-like macro since there's no possible way it will ever expand differently.

```glsl
#define AZ 7
#define FOO A##Z - 5

FOO // Expands to: 7 - 5

// FOO → A##Z - 5    The FOO macro is first expanded
//           ↓
//        AZ - 5     The token concatenation operator is applied
//           ↓
//         7 - 5     The AZ macro is expanded
```
### Function-like
A function-like macro is one which accepts arguments and is subsituted by replacement tokens:
```glsl
#define _NAME( ) _REPLACEMENT-LIST_
#define _NAME_( _PARAM_ ) _REPLACEMENT-LIST_
#define _NAME_( _PARAM_, ... ) _REPLACEMENT-LIST_

// Examples:
#define FOOBAR()
#define ADD( A, B ) A + B
#define CONCAT(A,B) A##B
```
`_NAME_` is the name of the macro. It is mandatory. For this to be a function-like macro, the immediate next token must an opening parenthesis `(` without any whitespace in-between.

`_PARAM_` is a name of a parameter.

`_REPLACEMENT-LIST_` is a list of tokens which will replace any invocation of this macro. It is optional. It can contain any GLSL tokens in any order (mismatched braces, invalid tokens, etc.), but if the macro is expanded the tokens will be checked for validity as normal. If this list is empty, invoking the macro will replace it with an empty string, i.e. remove it.

To call a function-like macro, the name of the macro must be followed by parenthesis:
```glsl
#define FOO()

// These call the macro:
FOO()
FOO ()

// But this doesn't:
FOO
```

When a function-like macro is called, the arguments passed in the brackets are mapped to the parameters in the definition. The arguments are split by a comma just like in a normal function call:
```glsl
#define ADD_10(A) (A) + 10

ADD(5) // Expands to: (5) + 10
ADD(5 * 8) // Expands to: (5 * 8) + 10
```

Arguments within a function-like macro are expanded before being passed into the macro:
```glsl
#define AZ 5;
#define BZ 0;

#define ADD_INT(_1) _1##Z + 10

ADD_INT(A)

ADD_INT(_1) is populated such that:
_1 = A

_1##Z + 10 -> A##Z + 10 -> AZ + 10 -> 5 + 10

// BAR -> FOO -> 8    The BAR macro is first expanded.
//               |
//              \/
//      ADD_10( 8 )   Then the result is actually passed to the macro call.
```
```glsl
#define NAME my_name
#define BAR NAME
#define DECLARE(a, b) a = b
#define INIT(a, b, c) DECLARE(a b, c)

INIT(int, BAR, 0)
↓                
Identify arguments:
a = int
b = BAR
c = 0
↓
Arguments are expanded since they're not concatenated:
a = int
b = my_name
c = 0
↓
Parameters in the body are replaced:
DECLARE(int my_name, 0)
↓

loop until no further expansions left:
DECLARE(int my_name, 0)
↓
a = int my_name
b = 0
↓
No expansion necessary
↓
int my_name = 0

FINISHED
```

If a function-like macro, the parameters are first replaced with the argument tokens, then any token concatenation occurs, then any further macro expansions occur. Note that an argument of `##` is not taken into account in regards to token concatenation.

### Nesting
Macros can be nested within other macros, and they will be expanded fully:
```glsl
#define FOO 5
#define BAR FOO + 8

int i = BAR; // Expands to: int i = 5 + 8;
```
The only limitation is that a macro which has already been visited in an expansion cannot be expanded again. Effectively, recursion is not allowed:
```glsl
#define FOO BAR
#define BAR FOO
#define BAZ BAR

BAZ // Expands to: BAR
// BAZ -> BAR -> FOO -> BAR
//                      ~~~ we've already visited this macro,
//                          it is not expanded, but inserted verbatim
```

### Re-defining
Macros can be re-defined only if:
- Both are the same type of macro.
- The tokens in the `_REPLACEMENT-LIST_` are identical.
- If a function-like macro, the parameters are identical.
- Whitespace appears in the same places.

For whitespace to appear in the same places, consult the examples below. The gist is that if there already is a whitespace, comments can be added since they are treated as whitespace. But if there is no whitespace, neither whitespace nor comments can be introduced in the re-definition. The whitespace rule only applies to the `_REPLACEMENT-LIST_`; whitespace can be introduced within the parameter list.
```glsl
#define FOO

// Valid:
#define FOO

// Invalid:
#define FOO 5
#define FOO( )

//---

#define BAR (1-1)

// Valid:
#define BAR      (1-1)
#define BAR /* aaa */ (1-1) // bbb

// Invalid:
#define BAR (1 - 1)
#define BAR (/* ooo */ 1 -1)

//---

#define BAZ(A) 5 -- - 8

// Valid:
#define BAZ(A)     5 --      -  8
#define BAZ(/* z */ A ) 5 /* ... */ -- - 8 // .......

// Invalid:
#define BAZ(B) 5 -- - 8
#define BAZ(A) 5 --- 8
```
A macro can always be un-defined and then defined as a new macro.

### Built-in
```glsl
// Always defined
#define GL_core_profile 1

// Defined if the profile is set to `compatibility`.
#define GL_compatibility_profile 1

// Defined if the profile is set to `es`
#define GL_es_profile 1
```
## undef
Un-defines a macro:
```glsl
#undef _IDENTIFIER_
```
`_IDENTIFIER_` specifies the name of the macro. If there is no macro with such a name, this directive is ignored. Even if the macro is a function-like macro, only the name is specified; the parenthesis are omitted.

## ifdef
⚠ `defined` can also be a valid macro name
```glsl
#ifdef SYMBOL
```
`SYMBOL` is any identifier string.

## ifndef
```glsl
#ifndef SYMBOL
```
`SYMBOL` is any identifier string.

## if
## elif
## else
```glsl
#else
```

## endif
```glsl
#endif
```

## error
Causes the compiler to produce a compile-time error and print the text in the debug log output:
```glsl
#error _TEXT_
```
`_TEXT_` is any number of any characters.

## pragma
Controls compiler options:
```glsl
#pragma _OPTIONS_
```
`_OPTIONS_` is any number of any characters.

TODO: Supported pragmas as part of the language.

## Macros
Macro names starting with the `GL_` prefix are reserved for OpenGL; they cannot de (un)defined. Macro names starting with a `__` prefix are by convention reserved; they can be (un)defined but it may cause unintended behaviour if a previous implementation definition exists.

### \_\_FILE\_\_
It is **not** a file name, since GLSL has no concept of files. It is a decimal integer representing which string in the list of strings the shader came from.

### \_\_LINE\_\_
The line number.

### \_\_VERSION\_\_
The version number as an integer, e.g. version 4.50 is `450`.