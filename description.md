 123456789 123456789 123456789 123456789 123456789 123456789 123456789 123456789

# Description of obfuscation algorithm using FAPKC

## Algebra

### Rings and fields

A **ring** is an algebra having at least two elements: zero and one, equiped
with operations: addition, subtraction and multiplication. If multiplication is
commutative it is called **commutative ring**. If it has finite number of
elements it is called **finite ring**.

A **field** is an algebra that in addition to field operations also has division
operation. Formally a field is an **extension** of a ring or, speaking
informally, a field becomes a ring if we drop the division operation. A field
may be finite or infinite. Multiplication in a field is always commutative.

Not every ring can be extended to a field.

### Modular fields

Consider integer numbers with operations: addition, subtraction, multiplication.
This structure is called the **integer ring**. Consider modular arithmetic where
each of these operations is taken modulo positive number `p` greater or equal 2.
Such structure is called **modular ring** and the number `p` is called the
**modulus**. A modular ring has exactly `p` elements therefore it is finite.

By abuse of notation we may denote modular rings by imposing a condition
`p = 0`.

Let's define **multiplicative inverse** of nonzero element `e` in a ring to be
such element `f` so that `e · f = 1 (mod p)`. Not every element has to have an
inverse. However if the modulus is a prime number every nonzero element has an
inverse. In such a ring it is possible to define division operation and thus
promote it to a **modular field**.

### Ring of polynomials

Let's define a special element `x`. Let's take formal natural powers of this
element: `x⁰, x¹, x², x³, ...` and let's assume all those elements are unequal.
Let's take some modular field (modulo `p`) and consider a formal product of an
element of the field with any power of `x`. Such a product is called a
**monomial**. Every monomial is characterized by the value of the field element
(called the **coefficient**) and the power standing above `x`. We can define
products of two monomials: `(a·x^m) · (b·x^n) = (a·b)·x^(m+n)` that is also a
monomial.

Addition and subtraction of monomials is defined only if the power of added
(or subtracted) monomials is the same: `(a·x^m) + (b·x^m) = (a+b)·x^m`.

Consider a formal sum of some number of monomials of different powers. Such an
object is called an **univariate polynomial** over a field. Summing univariate
polynomials means adding field elements at the monomials of matching powers.

```
  (a[0]·x^0 + a[1]·x^1 + ... a[n]·x^n) +
+ (b[0]·x^0 + b[1]·x^1 + ... b[m]·x^m) =
= (a[0]+b[0])·x^0 + (a[1]+b[1])·x^1 + ... + (a[k]+b[k])·x^k

k = max(m, n)
```

It is important to remember that addition is done in modular field.
Subtraction is defined analogously.

We assume that monomials missing from the sum have coefficient of zero. The
highest power of all monomials is called the **degree** of the polynomial.
A polynomial where all coefficients are zero is called zero polynomial, and
such a polynomial does not have a degree.

Product of two polynomials is given by the formula:

```
  (a[0]·x^0 + a[1]·x^1 + ... a[n]·x^n) ·
· (b[0]·x^0 + b[1]·x^1 + ... b[m]·x^m) =
= a[0]·b[0]·x^0 + a[1]·b[0]·x^1 + ... + a[n]·b[0]·x^n +
                + a[0]·b[1]·x^1 + ... + a[n]·b[1]·x^(n+1) +
                                + ... +
                                + ... + a[n]·b[m]·x^(n+m)
```

Such structure with addition, subtraction and multiplication fulfills the
definition of a ring and therefore is called the **ring of polynomials**
over modular field.

### Euclidean division of polynomials

**Euclidean division** of polynomials, also called **division with rest**
is an operation that given two polynomials: `a` (the **dividend**),
`b` (the **divisior**) returns two polynomials: `q` (the **quotient**) and
`r` (the **remainder**) such that: `a = q·b + r`. In the context of division
the value `r` may also be called the "rest". The degree of `r` is always
smaller or equal to the degree of `b`. Division is not defined if `b` is
zero.

There exists an algorithm to find the quotient and remainder broadly cited
in literature under the name "polynomial Euclidean division" or "polynomial
long division". While it is usually defined for polynomials over integer
or real numbers, it also generalizes to polynomials over fields, so also
over modular fields. Whenever a coefficient division is requested in the
algorithm, we must use division from the right field.

Now it is possible to define **modulo operation** on two polynomials that
simply returns the remainder.

If a remainder happens to be zero, the polynomial `a` is said to be
**divisible** by `b` and there exists such `q` so that `a = q·b`. Any two
`q`, `b` that are not equal to zero or one are called **factorization** of
a polynomial. If a polynomial does not have any factorization then it is
called **irreducible**. Whether a polynomial is reducible is dependent of
the particular field it is defined over, i.e. two polynomials of the same
form but over different fields may have different factorizations.

### Galois fields

In a way that is analogous to construction of modular rings from the
integer ring, it is possible to define modular arithmetics of polynomials.
Let's take some polynomial that will be called the **reducing polynomial**.
Let's define modular addition, modular subtraction and modular
multiplication by first adding (subtracting or multiplying) two
polynomials and then finding the remainder with respect to the chosen
modulus. Such a structure is also a ring. By abuse of notation it may be
denoted by imposing a condition `b = 0` where `b` is the reducing
polynomial.

By analogy to constuction of modular fields let's now consider
multiplicative inverse of elements of this ring. In modular rings' case
every element had an inverse if the modulus `p` was prime. In polynomials'
case a similar effect is obtained by taking an irreducible polynomial `b`.

If the polynomial modulus is an irreducible polynomial, every nonzero
element of the modular polynomial ring has an inverse and therefore can
be extended to a field. Such a field is called a **Galois field**. Every
Galois field is finite and has number of elements equal to `p^n` where
`n` is the degree of the reducing polynomial and `p` is the prime modulus
of the backing modular field.

Every finite field may be obtained by that construction. Performing this
construction again with a Galois field in place of the modular field
yields again a Galois field. Every two Galois field with different
reducing polynomials of the same degree and over the same modular field
are isomorphic but not equal. Taking reducing polynomials of the form
`x - 1` yields fields isomorphic to the modular field the reducing
polynomial was defined over.

### Exponent and logarithm in a Galois field

Let's take a Galois field with reducing polynomial `b` over a modular field
with modulus `p`. Let `n` be the degree of the reducing polynomial `b`.
The number of elements of this field is `p^n`.

In every such Galois field every element taken to the power `p^n` gives
again the same element.

`k^(p^n) = k`

`k` is an element of the field. It is worth noting that the first
exponentiation symbol means repeated multiplication in the field, but the
second one is a regular numeric exponentiation.

From there, it follows that:

`k^(p^n - 1) = i`

Where `i` is the "one" element of the field, the neutral element of multiplication.

It can be shown that exponentiation in a Galois field forms a cyclic group, that
means `k^m = k^(m % (p^n - 1))` where we used the percentage symbol to denote
numeric modulo operation.

In every field there exists an element such that rising it to increasing powers
yields all elements of the field, except zero. Such element is called a
**generator** of that field. It is possible to define two operations: exponent
and logarithm, with respect to a fixed generator.

Exponent is a function that takes an integer and returns a field element, equal
to the generator rised to the power of the provided argument. Logarithm takes
any nonzero element of the field and returns an integer that would give back
the original element if the generator was rised to that power. Both functions
may be implemented using lookup tables.

It is possible to implement multiplication, division and inverse operaton using
the provided exponent and logarithm functions, using the identities:

`a · b = exp[(log[a] + log[b]) % (p^n - 1)]`
`a / b = exp[(log[a] - log[b]) % (p^n - 1)]`
`b^(-1) = exp[(-log[b]) % (p^n - 1)]`

### Polynomials as functions

There are some commonly defined operations on polynomials that are not ring
operations.

Let's take a polynomial over some finite field.

**Evaluating** a polynomial at a point means substituting the variable `x`
for a field element and performing all the remaining operations in the
field. A polynomial thus defines a function, however it is not guaranteed
that these functions are different. In fact, since in every field `k^(p^n - 1) = i`
all monomials above `p^n - 1` are redundant.

Every function of one argument in Galois field may be represented by some polynomial
of maximum degree `p^n - 1`.

**Composition** two polynomials means substituting the variable in one polynomial `x` for another
polynomial and then performing all the remaining operations in the ring
of polynomials. The function computed by the composition of polynomials is a composition
of functions computed by each polynomial.

**Decomposition** of a polynomial means searching for two polynomials that give back
the original one when composed.

### Additive functions in Galois fields

Let's take a Galois field with reducing polynomial `b` over a modular field
with modulus `p`. Let `n` be the degree of the reducing polynomial `b`.
The number of elements of this field is `p^n`.

In every such field, for any two elements `k` and `l` it holds that: `(k + l)^p = k^p + l^p`.
Or in other words, the function `f(x) = x^p` is distributive with respect to addition.
Composing the function `f(x) = x^p` with itself gives the function `g(x) = x^(p^2)` that is
also distributive w.r.t. addition. In fact, every function of the form `h(x) = x^(p^n)` and
every linear combination of such functions is distributive w.r.t. addition. We will call them
**additive functions**. Every such function can be represented as:
`k[0]·x^(p^0) + k[1]·x^(p^1) + ... + k[n-1]·x^(p^(n-1))`.

Every element of a Galois field can be regarded as a polynomial over modular field with modulus
`p` with maximum degree `n`. Let's take the coefficients of that polynomial and form a vector
with `n` elements from modular field with modulus `p`. Now let's take a square matrix `n×n` with
elements from that modular field. There is 1-to-1 correspondence between such matrices and additive
functions defined above. Every such function acting on a Galois field may be interpreted as a
square matrix acting on vectors over the backing modular field.


a[0]·x^0 + a[1]·x^1 + ... + a[n-1]·x^(n-1)
{a[0], a[1], ..., a[n-1]}

a[0]·b[1]·x^1 + a[1]·b[1]·x^2 + ... + a[n-1]·b[1]·x^n



k[0]·x^(p^0) + k[1]·x^(p^1) + ... + k[n-1]·x^(p^(n-1))


0 1 0 0 0 0 0 0
0 0 1 0 0 0 0 0
0 0 0 1 0 0 0 0
0 0 0 0 1 0 0 0
0 0 0 0 0 1 0 0
0 0 0 0 0 0 1 0
0 0 0 0 0 0 0 1
1 0 1 1 0 0 0 1





## Circuits

### Definition

**Circuit** is a machine that does not have any memory, i.e. permanent state.

Formally, a circuit is defined by a function `f` from a finite input alphabet to a finite output alphabet.
A circuit is a machine consuming an input tape with symbols from input alphabet and produces a tape with
symbols from output alphabet. The tapes are related by the formula: `o[t] = f(i[t])`.

Let's take some finite field `F`. Let's take the input alphabet as vectors of length `m` over the field `F`.
Let's take the output alphabet as vectors of length `m` over the field `F`. Every circuit with such alphabets
may be represented as directed acyclic graph of **gates**. A gate has a set of input lines and output lines.
There are also argument vertices and result vertices. Each line carries a value from the field `F`.
A gate takes the values from the input lines, performs an operation and returns the result over all output
lines. Result vertices take only one input line. Directed cycles are not allowed.

In a field only two types of gates are necessary: adding gate and multiplying gate, but for convinence we
will also use subtracting gate (that takes exactly 2 labelled input lines) and multiplication by constant
gate (that takes exactly 1 input line and has a label that is a constant from the field `F`).

### Linear circuits

A circuit featuring only linear gates is called a **linear circuit**. Such a circuit may be represented by
`m×n` additive functions.

### Quadratic circuits

## Transducers

## Memory transducers

## Linear transducers

## Quadratic transducers

## FAPKC

### RaRb algorithm

The procedure known as RaRb algorithm is what allows generating pairs of mutually inverse transducers.
On algebraic level it is a series of matrix transformations.

Let's start with memory transducer defined by the formula:
`y[t] = A[0](x[t]) + A[1](x[t-1]) + ... + A[k](x[t-k])`.
The task is to find a formula defining a transducer taking `y` and returning `x`. None of the matrices
`A` is invertible, as if that was the case, the single matrix could be inverted, yielding the right formula.

We write down the defining equation, repeated `k` times for each point of time from `t` to `t-k`.

```
y[t]   = A[0](x[t])   + A[1](x[t-1])   + ... + A[k](x[t-k])
y[t-1] = A[0](x[t-1]) + A[1](x[t-2])   + ... + A[k](x[t-k-1])
...
y[t-k] = A[0](x[t-k]) + A[1](x[t-k-1]) + ... + A[k](x[t-2·k])
```

We can separate the matrices on the right, if they depend on `x[t] ... x[t-k]` or `x[t-k-1] ... x[t-2·k]`.
Then we can arrange them into two big matrices `Al` and `Ar`, acting on formal vectors `{x[t], ..., x[t-k]}`,
`{x[t-k-1] ... x[t-2·k]}`. The matrix `Al` is a square `k×k` matrix whose only nonzero elements lie on the top left
of the secondary diagonal, and on the diagonal itself. The matrix `Ar` is a rectangular `k×(k-1)` matrix whose
only nonzero elements lie on the bottom right of the secondary diagonal, and the diagonal itself is zero. For
convenience we may extend the matrix `Ar` by a row of zeros on the top and make it act on the vector `{x[t-k] ... x[t-2·k]}`.
Still, the result of that matrix does not depend on the value `x[t-k]`.

```
{y[t], ..., y[t-k]} = Al·{x[t], ..., x[t-k]} + Ar·{x[t-k], ..., x[t-2·k]}
```

There exists a polynomial algorithm whose input is the matrix `Al`, producing a square `k×k` matrix `P`, such that
the top left submatrix of `P·Al` is invertible.


Take the matrix `P` and multiply the formula by it on the left.

```
P·{y[t], ..., y[t-k]} = P·Al·{x[t], ..., x[t-k]} + P·Ar·{x[t-k], ..., x[t-2·k]}
```

Now we are interested only in the first row of the resulting formula. Let's treat the first rows of matrices `P`, `Al`, `Ar`
as formal vectors and let's use notation for scalar product.

```
P[0]·{y[t], ..., y[t-k]} = (P·Al)[0]·{x[t], ..., x[t-k]} + (P·Ar)[0]·{x[t-k], ..., x[t-2·k]}
SUM(l) P[0][l]·y[t-l] = SUM(l) (P·Al)[0][l]·x[t-l] + SUM(l) (P·Ar)[0][l]·x[t-k-l]
```

The vector `(P·Ar)[0]` equals zero, so the values `x[t-k-1], ..., x[t-2·k]` never appear in the equation.

```
SUM(l) P[0][l]·y[t-l] = SUM(l) (P·Al)[0][l]·x[t-l]
```

Now to recover `x[0]` we need to isolate the term that contains it, move it to one side of the equation and
then multiply the equation by the inverse of the matrix `(P·Al)[0][0]`.

```
x[0] = (P·Al)[0][0]^(-1) (SUM(l=0...k) P[0][l]·y[t-l] - SUM(l=1...k) (P·Al)[0][l]·x[t-l])
```

This is the definition formula for a memory transducer. It is a weak inverse of the transducer defined by (1), with delay `k`.

## FAPKC versions 0, 1, 93 and 2

Early versions of FAPKC postulated generating 2 pairs of transducers. A linear pair with delay, generated through RaRb algorithm
and a nonlinear pair with delay 0, whose inverse was calculated simply by inverting the matrix standing at `x[0]`. One linear and
one nonlinear transducer were then commposed to give the public key. The inverses of the two were composed in reverse order to
give the private key. The resulting transducers had delay `k`.

Those versions proved to be vunerable to an attack described in [...], allowing complete factorization of the public key.


## FAPKC versions 3 and 4

FAPKC version 3 changed the way the nonlinear transducer is generated. First, a pair of linear transducers with delay `l` is created by algorithm
RaRb. Then a nonlinear part that does not depend on `x[0]` is added to the first one and subtracted from the second one. The result
is a separable nonlinear transducer and its inverse with delay `l`.

The transducers were then composed into public and private key, giving two automata with delay `k+l`.

