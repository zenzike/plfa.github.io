---
src       : src/plfa/Negation.lagda
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
---

<pre class="Agda">{% raw %}<a id="189" class="Keyword">module</a> <a id="196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}" class="Module">plfa.Negation</a> <a id="210" class="Keyword">where</a>{% endraw %}</pre>

This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

<pre class="Agda">{% raw %}<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="388" class="Keyword">using</a> <a id="394" class="Symbol">(</a><a id="395" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="398" class="Symbol">)</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="421" class="Keyword">using</a> <a id="427" class="Symbol">(</a><a id="428" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="429" class="Symbol">;</a> <a id="431" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="435" class="Symbol">;</a> <a id="437" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="440" class="Symbol">)</a>
<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="https://agda.github.io/agda-stdlib/Data.Empty.html" class="Module">Data.Empty</a> <a id="465" class="Keyword">using</a> <a id="471" class="Symbol">(</a><a id="472" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a><a id="473" class="Symbol">;</a> <a id="475" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a><a id="481" class="Symbol">)</a>
<a id="483" class="Keyword">open</a> <a id="488" class="Keyword">import</a> <a id="495" href="https://agda.github.io/agda-stdlib/Data.Sum.html" class="Module">Data.Sum</a> <a id="504" class="Keyword">using</a> <a id="510" class="Symbol">(</a><a id="511" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#419" class="Datatype Operator">_⊎_</a><a id="514" class="Symbol">;</a> <a id="516" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#475" class="InductiveConstructor">inj₁</a><a id="520" class="Symbol">;</a> <a id="522" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#500" class="InductiveConstructor">inj₂</a><a id="526" class="Symbol">)</a>
<a id="528" class="Keyword">open</a> <a id="533" class="Keyword">import</a> <a id="540" href="https://agda.github.io/agda-stdlib/Data.Product.html" class="Module">Data.Product</a> <a id="553" class="Keyword">using</a> <a id="559" class="Symbol">(</a><a id="560" href="https://agda.github.io/agda-stdlib/Data.Product.html#1353" class="Function Operator">_×_</a><a id="563" class="Symbol">)</a>
<a id="565" class="Keyword">open</a> <a id="570" class="Keyword">import</a> <a id="577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="594" class="Keyword">using</a> <a id="600" class="Symbol">(</a><a id="601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4092" class="Record Operator">_≃_</a><a id="604" class="Symbol">;</a> <a id="606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2736" class="Postulate">extensionality</a><a id="620" class="Symbol">)</a>{% endraw %}</pre>


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false:
<pre class="Agda">{% raw %}<a id="¬_"></a><a id="816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬_</a> <a id="819" class="Symbol">:</a> <a id="821" class="PrimitiveType">Set</a> <a id="825" class="Symbol">→</a> <a id="827" class="PrimitiveType">Set</a>
<a id="831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#833" class="Bound">A</a> <a id="835" class="Symbol">=</a> <a id="837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#833" class="Bound">A</a> <a id="839" class="Symbol">→</a> <a id="841" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>{% endraw %}</pre>
This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction:
<pre class="Agda">{% raw %}<a id="¬-elim"></a><a id="1413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1413" class="Function">¬-elim</a> <a id="1420" class="Symbol">:</a> <a id="1422" class="Symbol">∀</a> <a id="1424" class="Symbol">{</a><a id="1425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1425" class="Bound">A</a> <a id="1427" class="Symbol">:</a> <a id="1429" class="PrimitiveType">Set</a><a id="1432" class="Symbol">}</a>
  <a id="1436" class="Symbol">→</a> <a id="1438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="1440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1425" class="Bound">A</a>
  <a id="1444" class="Symbol">→</a> <a id="1446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1425" class="Bound">A</a>
    <a id="1452" class="Comment">---</a>
  <a id="1458" class="Symbol">→</a> <a id="1460" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="1462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1413" class="Function">¬-elim</a> <a id="1469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1469" class="Bound">¬x</a> <a id="1472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1472" class="Bound">x</a> <a id="1474" class="Symbol">=</a> <a id="1476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1469" class="Bound">¬x</a> <a id="1479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1472" class="Bound">x</a>{% endraw %}</pre>
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else:
<pre class="Agda">{% raw %}<a id="1880" class="Keyword">infix</a> <a id="1886" class="Number">3</a> <a id="1888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬_</a>{% endraw %}</pre>
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
<pre class="Agda">{% raw %}<a id="¬¬-intro"></a><a id="2193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2193" class="Function">¬¬-intro</a> <a id="2202" class="Symbol">:</a> <a id="2204" class="Symbol">∀</a> <a id="2206" class="Symbol">{</a><a id="2207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2207" class="Bound">A</a> <a id="2209" class="Symbol">:</a> <a id="2211" class="PrimitiveType">Set</a><a id="2214" class="Symbol">}</a>
  <a id="2218" class="Symbol">→</a> <a id="2220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2207" class="Bound">A</a>
    <a id="2226" class="Comment">-----</a>
  <a id="2234" class="Symbol">→</a> <a id="2236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2207" class="Bound">A</a>
<a id="2242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2193" class="Function">¬¬-intro</a> <a id="2251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2251" class="Bound">x</a>  <a id="2254" class="Symbol">=</a>  <a id="2257" class="Symbol">λ{</a><a id="2259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2259" class="Bound">¬x</a> <a id="2262" class="Symbol">→</a> <a id="2264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2259" class="Bound">¬x</a> <a id="2267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2251" class="Bound">x</a><a id="2268" class="Symbol">}</a>{% endraw %}</pre>
Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

An equivalent way to write the above is as follows:
<pre class="Agda">{% raw %}<a id="¬¬-intro′"></a><a id="2591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2591" class="Function">¬¬-intro′</a> <a id="2601" class="Symbol">:</a> <a id="2603" class="Symbol">∀</a> <a id="2605" class="Symbol">{</a><a id="2606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2606" class="Bound">A</a> <a id="2608" class="Symbol">:</a> <a id="2610" class="PrimitiveType">Set</a><a id="2613" class="Symbol">}</a>
  <a id="2617" class="Symbol">→</a> <a id="2619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2606" class="Bound">A</a>
    <a id="2625" class="Comment">-----</a>
  <a id="2633" class="Symbol">→</a> <a id="2635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2606" class="Bound">A</a>
<a id="2641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2591" class="Function">¬¬-intro′</a> <a id="2651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2651" class="Bound">x</a> <a id="2653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2653" class="Bound">¬x</a> <a id="2656" class="Symbol">=</a> <a id="2658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2653" class="Bound">¬x</a> <a id="2661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2651" class="Bound">x</a>{% endraw %}</pre>
Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
<pre class="Agda">{% raw %}<a id="¬¬¬-elim"></a><a id="2943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2943" class="Function">¬¬¬-elim</a> <a id="2952" class="Symbol">:</a> <a id="2954" class="Symbol">∀</a> <a id="2956" class="Symbol">{</a><a id="2957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2957" class="Bound">A</a> <a id="2959" class="Symbol">:</a> <a id="2961" class="PrimitiveType">Set</a><a id="2964" class="Symbol">}</a>
  <a id="2968" class="Symbol">→</a> <a id="2970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2957" class="Bound">A</a>
    <a id="2982" class="Comment">-------</a>
  <a id="2992" class="Symbol">→</a> <a id="2994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="2996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2957" class="Bound">A</a>
<a id="2998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2943" class="Function">¬¬¬-elim</a> <a id="3007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3007" class="Bound">¬¬¬x</a>  <a id="3013" class="Symbol">=</a>  <a id="3016" class="Symbol">λ</a> <a id="3018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3018" class="Bound">x</a> <a id="3020" class="Symbol">→</a> <a id="3022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3007" class="Bound">¬¬¬x</a> <a id="3027" class="Symbol">(</a><a id="3028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2193" class="Function">¬¬-intro</a> <a id="3037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3018" class="Bound">x</a><a id="3038" class="Symbol">)</a>
<a id="3040" class="Comment">-- ¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)</a>{% endraw %}</pre>
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`:
<pre class="Agda">{% raw %}<a id="contraposition"></a><a id="3555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3555" class="Function">contraposition</a> <a id="3570" class="Symbol">:</a> <a id="3572" class="Symbol">∀</a> <a id="3574" class="Symbol">{</a><a id="3575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3575" class="Bound">A</a> <a id="3577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3577" class="Bound">B</a> <a id="3579" class="Symbol">:</a> <a id="3581" class="PrimitiveType">Set</a><a id="3584" class="Symbol">}</a>
  <a id="3588" class="Symbol">→</a> <a id="3590" class="Symbol">(</a><a id="3591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3575" class="Bound">A</a> <a id="3593" class="Symbol">→</a> <a id="3595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3577" class="Bound">B</a><a id="3596" class="Symbol">)</a>
    <a id="3602" class="Comment">-----------</a>
  <a id="3616" class="Symbol">→</a> <a id="3618" class="Symbol">(</a><a id="3619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="3621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3577" class="Bound">B</a> <a id="3623" class="Symbol">→</a> <a id="3625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="3627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3575" class="Bound">A</a><a id="3628" class="Symbol">)</a>
<a id="3630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3555" class="Function">contraposition</a> <a id="3645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3645" class="Bound">f</a> <a id="3647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3647" class="Bound">¬y</a> <a id="3650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3650" class="Bound">x</a> <a id="3652" class="Symbol">=</a> <a id="3654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3647" class="Bound">¬y</a> <a id="3657" class="Symbol">(</a><a id="3658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3645" class="Bound">f</a> <a id="3660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3650" class="Bound">x</a><a id="3661" class="Symbol">)</a>{% endraw %}</pre>
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.

Using negation, it is straightforward to define inequality:
<pre class="Agda">{% raw %}<a id="_≢_"></a><a id="4093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4093" class="Function Operator">_≢_</a> <a id="4097" class="Symbol">:</a> <a id="4099" class="Symbol">∀</a> <a id="4101" class="Symbol">{</a><a id="4102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4102" class="Bound">A</a> <a id="4104" class="Symbol">:</a> <a id="4106" class="PrimitiveType">Set</a><a id="4109" class="Symbol">}</a> <a id="4111" class="Symbol">→</a> <a id="4113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4102" class="Bound">A</a> <a id="4115" class="Symbol">→</a> <a id="4117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4102" class="Bound">A</a> <a id="4119" class="Symbol">→</a> <a id="4121" class="PrimitiveType">Set</a>
<a id="4125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4125" class="Bound">x</a> <a id="4127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4093" class="Function Operator">≢</a> <a id="4129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4129" class="Bound">y</a>  <a id="4132" class="Symbol">=</a>  <a id="4135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="4137" class="Symbol">(</a><a id="4138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4125" class="Bound">x</a> <a id="4140" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="4142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4129" class="Bound">y</a><a id="4143" class="Symbol">)</a>{% endraw %}</pre>
It is trivial to show distinct numbers are not equal:
<pre class="Agda">{% raw %}<a id="4223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4223" class="Function">_</a> <a id="4225" class="Symbol">:</a> <a id="4227" class="Number">1</a> <a id="4229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4093" class="Function Operator">≢</a> <a id="4231" class="Number">2</a>
<a id="4233" class="Symbol">_</a> <a id="4235" class="Symbol">=</a> <a id="4237" class="Symbol">λ()</a>{% endraw %}</pre>
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number:
<pre class="Agda">{% raw %}<a id="peano"></a><a id="4646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4646" class="Function">peano</a> <a id="4652" class="Symbol">:</a> <a id="4654" class="Symbol">∀</a> <a id="4656" class="Symbol">{</a><a id="4657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4657" class="Bound">m</a> <a id="4659" class="Symbol">:</a> <a id="4661" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4662" class="Symbol">}</a> <a id="4664" class="Symbol">→</a> <a id="4666" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="4671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4093" class="Function Operator">≢</a> <a id="4673" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4657" class="Bound">m</a>
<a id="4679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4646" class="Function">peano</a> <a id="4685" class="Symbol">=</a> <a id="4687" class="Symbol">λ()</a>{% endraw %}</pre>
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways:
<pre class="Agda">{% raw %}<a id="id"></a><a id="5189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5189" class="Function">id</a> <a id="5192" class="Symbol">:</a> <a id="5194" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a> <a id="5196" class="Symbol">→</a> <a id="5198" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="5200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5189" class="Function">id</a> <a id="5203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5203" class="Bound">x</a> <a id="5205" class="Symbol">=</a> <a id="5207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5203" class="Bound">x</a>

<a id="id′"></a><a id="5210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5210" class="Function">id′</a> <a id="5214" class="Symbol">:</a> <a id="5216" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a> <a id="5218" class="Symbol">→</a> <a id="5220" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="5222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5210" class="Function">id′</a> <a id="5226" class="Symbol">()</a>{% endraw %}</pre>
But, using extensionality, we can prove these equal:
<pre class="Agda">{% raw %}<a id="id≡id′"></a><a id="5306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5306" class="Function">id≡id′</a> <a id="5313" class="Symbol">:</a> <a id="5315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5189" class="Function">id</a> <a id="5318" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5210" class="Function">id′</a>
<a id="5324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5306" class="Function">id≡id′</a> <a id="5331" class="Symbol">=</a> <a id="5333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2736" class="Postulate">extensionality</a> <a id="5348" class="Symbol">(λ())</a>{% endraw %}</pre>
By extensionality, `id ≡ id′` holds if for every
`x` in their domain we have `id x ≡ id′ x`. But there
is no `x` in their domain, so the equality holds trivially.

Indeed, we can show any two proofs of a negation are equal:
<pre class="Agda">{% raw %}<a id="assimilation"></a><a id="5602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5602" class="Function">assimilation</a> <a id="5615" class="Symbol">:</a> <a id="5617" class="Symbol">∀</a> <a id="5619" class="Symbol">{</a><a id="5620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5620" class="Bound">A</a> <a id="5622" class="Symbol">:</a> <a id="5624" class="PrimitiveType">Set</a><a id="5627" class="Symbol">}</a> <a id="5629" class="Symbol">(</a><a id="5630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5630" class="Bound">¬x</a> <a id="5633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5633" class="Bound">¬x′</a> <a id="5637" class="Symbol">:</a> <a id="5639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="5641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5620" class="Bound">A</a><a id="5642" class="Symbol">)</a> <a id="5644" class="Symbol">→</a> <a id="5646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5630" class="Bound">¬x</a> <a id="5649" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5633" class="Bound">¬x′</a>
<a id="5655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5602" class="Function">assimilation</a> <a id="5668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5668" class="Bound">¬x</a> <a id="5671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5671" class="Bound">¬x′</a> <a id="5675" class="Symbol">=</a> <a id="5677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2736" class="Postulate">extensionality</a> <a id="5692" class="Symbol">(λ</a> <a id="5695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5695" class="Bound">x</a> <a id="5697" class="Symbol">→</a> <a id="5699" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a> <a id="5706" class="Symbol">(</a><a id="5707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5668" class="Bound">¬x</a> <a id="5710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5695" class="Bound">x</a><a id="5711" class="Symbol">))</a>{% endraw %}</pre>
Evidence for `¬ A` implies that any evidence of `A`
immediately leads to a contradiction.  But extensionality
quantifies over all `x` such that `A` holds, hence any
such `x` immediately leads to a contradiction,
again causing the equality to hold trivially.


#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}{% link out/plfa/Relations.md%}#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

<pre class="Agda">{% raw %}<a id="6175" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}{% link out/plfa/Relations.md%}#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

<pre class="Agda">{% raw %}<a id="6575" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

<pre class="Agda">{% raw %}<a id="6863" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?


## Intuitive and Classical logic

In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows:
<pre class="Agda">{% raw %}<a id="9415" class="Keyword">postulate</a>
  <a id="em"></a><a id="9427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9427" class="Postulate">em</a> <a id="9430" class="Symbol">:</a> <a id="9432" class="Symbol">∀</a> <a id="9434" class="Symbol">{</a><a id="9435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9435" class="Bound">A</a> <a id="9437" class="Symbol">:</a> <a id="9439" class="PrimitiveType">Set</a><a id="9442" class="Symbol">}</a> <a id="9444" class="Symbol">→</a> <a id="9446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9435" class="Bound">A</a> <a id="9448" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="9450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="9452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9435" class="Bound">A</a>{% endraw %}</pre>
As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable):
<pre class="Agda">{% raw %}<a id="em-irrefutable"></a><a id="9712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9712" class="Function">em-irrefutable</a> <a id="9727" class="Symbol">:</a> <a id="9729" class="Symbol">∀</a> <a id="9731" class="Symbol">{</a><a id="9732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9732" class="Bound">A</a> <a id="9734" class="Symbol">:</a> <a id="9736" class="PrimitiveType">Set</a><a id="9739" class="Symbol">}</a> <a id="9741" class="Symbol">→</a> <a id="9743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="9745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="9747" class="Symbol">(</a><a id="9748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9732" class="Bound">A</a> <a id="9750" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="9752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="9754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9732" class="Bound">A</a><a id="9755" class="Symbol">)</a>
<a id="9757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9712" class="Function">em-irrefutable</a> <a id="9772" class="Symbol">=</a> <a id="9774" class="Symbol">λ</a> <a id="9776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9776" class="Bound">k</a> <a id="9778" class="Symbol">→</a> <a id="9780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9776" class="Bound">k</a> <a id="9782" class="Symbol">(</a><a id="9783" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#500" class="InductiveConstructor">inj₂</a> <a id="9788" class="Symbol">(λ</a> <a id="9791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9791" class="Bound">x</a> <a id="9793" class="Symbol">→</a> <a id="9795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9776" class="Bound">k</a> <a id="9797" class="Symbol">(</a><a id="9798" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#475" class="InductiveConstructor">inj₁</a> <a id="9803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9791" class="Bound">x</a><a id="9804" class="Symbol">)))</a>{% endraw %}</pre>
The best way to explain this code is to develop it interactively:

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that given a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly:

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct:

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly:

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct:

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof.

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)


#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

<pre class="Agda">{% raw %}<a id="13209" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
<pre class="Agda">{% raw %}<a id="Stable"></a><a id="13368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13368" class="Function">Stable</a> <a id="13375" class="Symbol">:</a> <a id="13377" class="PrimitiveType">Set</a> <a id="13381" class="Symbol">→</a> <a id="13383" class="PrimitiveType">Set</a>
<a id="13387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13368" class="Function">Stable</a> <a id="13394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13394" class="Bound">A</a> <a id="13396" class="Symbol">=</a> <a id="13398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="13400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#816" class="Function Operator">¬</a> <a id="13402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13394" class="Bound">A</a> <a id="13404" class="Symbol">→</a> <a id="13406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13394" class="Bound">A</a>{% endraw %}</pre>
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

<pre class="Agda">{% raw %}<a id="13533" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library:
<pre class="Agda">{% raw %}<a id="13685" class="Keyword">import</a> <a id="13692" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="13709" class="Keyword">using</a> <a id="13715" class="Symbol">(</a><a id="13716" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="13718" class="Symbol">)</a>
<a id="13720" class="Keyword">import</a> <a id="13727" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="13753" class="Keyword">using</a> <a id="13759" class="Symbol">(</a><a id="13760" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html#688" class="Function">contraposition</a><a id="13774" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode:

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
