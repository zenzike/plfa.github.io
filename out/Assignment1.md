---
src       : tspl/Assignment1.lagda
title     : "Assignment1: PUC Assignment 1"
layout    : page
permalink : /Assignment1/
---

<pre class="Agda">{% raw %}<a id="110" class="Keyword">module</a> <a id="117" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}" class="Module">Assignment1</a> <a id="129" class="Keyword">where</a>{% endraw %}</pre>

## YOUR NAME AND EMAIL GOES HERE

## Introduction

This assignment is due **1pm Friday 26 April**.

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Submit your homework using the "submit" command.
Please ensure your files execute correctly under Agda!

## Imports

<pre class="Agda">{% raw %}<a id="669" class="Keyword">import</a> <a id="676" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="714" class="Symbol">as</a> <a id="717" class="Module">Eq</a>
<a id="720" class="Keyword">open</a> <a id="725" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="728" class="Keyword">using</a> <a id="734" class="Symbol">(</a><a id="735" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="738" class="Symbol">;</a> <a id="740" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="744" class="Symbol">;</a> <a id="746" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="750" class="Symbol">;</a> <a id="752" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="755" class="Symbol">)</a>
<a id="757" class="Keyword">open</a> <a id="762" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3975" class="Module">Eq.≡-Reasoning</a> <a id="777" class="Keyword">using</a> <a id="783" class="Symbol">(</a><a id="784" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin_</a><a id="790" class="Symbol">;</a> <a id="792" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">_≡⟨⟩_</a><a id="797" class="Symbol">;</a> <a id="799" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">_≡⟨_⟩_</a><a id="805" class="Symbol">;</a> <a id="807" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">_∎</a><a id="809" class="Symbol">)</a>
<a id="811" class="Keyword">open</a> <a id="816" class="Keyword">import</a> <a id="823" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="832" class="Keyword">using</a> <a id="838" class="Symbol">(</a><a id="839" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="840" class="Symbol">;</a> <a id="842" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="846" class="Symbol">;</a> <a id="848" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="851" class="Symbol">;</a> <a id="853" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="856" class="Symbol">;</a> <a id="858" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="861" class="Symbol">;</a> <a id="863" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="866" class="Symbol">;</a> <a id="868" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#845" class="Datatype Operator">_≤_</a><a id="871" class="Symbol">;</a> <a id="873" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#868" class="InductiveConstructor">z≤n</a><a id="876" class="Symbol">;</a> <a id="878" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#910" class="InductiveConstructor">s≤s</a><a id="881" class="Symbol">)</a>
<a id="883" class="Keyword">open</a> <a id="888" class="Keyword">import</a> <a id="895" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="915" class="Keyword">using</a> <a id="921" class="Symbol">(</a><a id="922" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9375" class="Function">+-assoc</a><a id="929" class="Symbol">;</a> <a id="931" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9531" class="Function">+-identityʳ</a><a id="942" class="Symbol">;</a> <a id="944" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9272" class="Function">+-suc</a><a id="949" class="Symbol">;</a> <a id="951" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="957" class="Symbol">;</a>
  <a id="961" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2115" class="Function">≤-refl</a><a id="967" class="Symbol">;</a> <a id="969" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2308" class="Function">≤-trans</a><a id="976" class="Symbol">;</a> <a id="978" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2165" class="Function">≤-antisym</a><a id="987" class="Symbol">;</a> <a id="989" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2420" class="Function">≤-total</a><a id="996" class="Symbol">;</a> <a id="998" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#12667" class="Function">+-monoʳ-≤</a><a id="1007" class="Symbol">;</a> <a id="1009" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#12577" class="Function">+-monoˡ-≤</a><a id="1018" class="Symbol">;</a> <a id="1020" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#12421" class="Function">+-mono-≤</a><a id="1028" class="Symbol">)</a>
<a id="1030" class="Keyword">open</a> <a id="1035" class="Keyword">import</a> <a id="1042" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1057" class="Keyword">using</a> <a id="1063" class="Symbol">(</a><a id="1064" href="plfa.Relations.html#18533" class="Datatype Operator">_&lt;_</a><a id="1067" class="Symbol">;</a> <a id="1069" href="plfa.Relations.html#18560" class="InductiveConstructor">z&lt;s</a><a id="1072" class="Symbol">;</a> <a id="1074" href="plfa.Relations.html#18617" class="InductiveConstructor">s&lt;s</a><a id="1077" class="Symbol">;</a> <a id="1079" href="plfa.Relations.html#21319" class="InductiveConstructor">zero</a><a id="1083" class="Symbol">;</a> <a id="1085" href="plfa.Relations.html#21361" class="InductiveConstructor">suc</a><a id="1088" class="Symbol">;</a> <a id="1090" href="plfa.Relations.html#21264" class="Datatype">even</a><a id="1094" class="Symbol">;</a> <a id="1096" href="plfa.Relations.html#21284" class="Datatype">odd</a><a id="1099" class="Symbol">)</a>{% endraw %}</pre>

## Naturals

#### Exercise `seven` {#seven}

Write out `7` in longhand.


#### Exercise `+-example` {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.


#### Exercise `*-example` {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.


#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
<pre class="Agda">{% raw %}<a id="1938" class="Keyword">data</a> <a id="Bin"></a><a id="1943" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1943" class="Datatype">Bin</a> <a id="1947" class="Symbol">:</a> <a id="1949" class="PrimitiveType">Set</a> <a id="1953" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="1961" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1961" class="InductiveConstructor">nil</a> <a id="1965" class="Symbol">:</a> <a id="1967" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1943" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="1973" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1973" class="InductiveConstructor Operator">x0_</a> <a id="1977" class="Symbol">:</a> <a id="1979" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1943" class="Datatype">Bin</a> <a id="1983" class="Symbol">→</a> <a id="1985" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1943" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="1991" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1991" class="InductiveConstructor Operator">x1_</a> <a id="1995" class="Symbol">:</a> <a id="1997" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1943" class="Datatype">Bin</a> <a id="2001" class="Symbol">→</a> <a id="2003" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1943" class="Datatype">Bin</a>{% endraw %}</pre>
For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

## Induction

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap} 

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Relations


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

\end{code}
(Hint: For each of these, you may first need to prove related
properties of `One`.)
