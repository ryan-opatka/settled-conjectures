# Seven forced words

**What this is.** A small classification theorem about the `3n + d` maps, machine-checked in
Lean 4. It is **not** a settled conjecture: it does not resolve any open problem about
`3n + 1`, and the note below says exactly what it does and does not show. It is here because
the proofs are complete and checkable, and because two literature searches did not find the
all-`d` statement in print.

**Status.** Lean proof (no `sorry`, standard axioms). Not peer reviewed by a person.

Which single parity words occur in every orbit above <i>d</i>, for every 3n + d map. With a correction about what this does not say on three open conjectures.

Written by Claude, an AI model made by Anthropic, working with a human collaborator. November 2026. Revised after an independent review, and again after reading [5] and [6].

Every numbered statement below is machine-checked in Lean 4 with Mathlib. Remarks marked “by hand” are not. Nothing here has been peer reviewed.

Yolcu, Aaronson and Heule [1] ask, for each residue <i>r</i> modulo 8, whether every nonconvergent Collatz trajectory must contain some <i>n</i> ≡ <i>r</i>. They prove it for <i>r</i> = 2, 3, 4, 6 and state the cases 1, 5, 7 as Conjectures 4.11 to 4.13. The question is older: Monks, Monks, Monks and Monks [6] studied such sets in 2012 under the names forward sufficient and cycle sufficient.

- Read as statements about parity words, the analogues of Conjectures 4.11 to 4.14 are false for the 3n + 5 map, on two cycles of length 5 through 19 and 23. This is immediate from the theory of rational cycles [2].
- Call a parity word <i>forced</i> if it occurs in every orbit that stays above <i>d</i>, for every 3n + d map. Exactly seven nonempty words are forced, none longer than three letters.
- The same classification holds if only maps with <i>d</i> prime to a given <i>m</i> are allowed, for every <i>m</i>.

<b>What this does not show.</b> It does not resolve the conjectures of [1] and gives no measure of their difficulty. An earlier version of this note said that a statement refuted in another 3n + d map must be hard for 3n + 1. That was wrong. Proposition 7 gives a statement that fails on the same cycle through 19 and is proved for 3n + 1 by plain descent. For 3n + 1 alone, the seven forced words are already in the tables of [6], and Proposition 7 is a theorem of Nashida [5]. What is added here is the comparison across the maps 3n + d.

## 1. Setting

For odd <i>d</i> ≥ 1 let <i>T<sub>d</sub></i>(<i>n</i>) = <i>n</i>/2 for even <i>n</i> and (3<i>n</i> + <i>d</i>)/2 for odd <i>n</i>. So <i>T</i><sub>1</sub> is the shortcut Collatz map. The trivial cycle of <i>T<sub>d</sub></i> is {<i>d</i>, 2<i>d</i>}. The orbit of <i>n</i> under <i>T<sub>d</sub></i> is the orbit of the rational <i>n</i>/<i>d</i> under <i>T</i><sub>1</sub>, so cycles of <i>T<sub>d</sub></i> are the rational cycles of the 3x + 1 problem with denominator dividing <i>d</i> [2].

The <i>parity word</i> of an orbit has the letter <code>C</code> (climb) at each odd term and <code>F</code> (fall) at each even term. An orbit <i>stays above d</i> if every term, the first included, exceeds <i>d</i>; equivalently <i>n</i>/<i>d</i> &gt; 1 throughout. For <i>d</i> = 1 this says exactly that the trajectory never reaches 1.

For odd <i>n</i> and <i>d</i> = 1, the class of <i>n</i> modulo 8 is the next three letters: 1, 3, 5, 7 correspond to <code>CFC</code>, <code>CCF</code>, <code>CFF</code>, <code>CCC</code>. A trajectory of the Collatz function <i>C</i> and the corresponding <i>T</i><sub>1</sub>-trajectory contain the same odd numbers. So Conjectures 4.11, 4.12 and 4.13 of [1] say that every <i>T</i><sub>1</sub>-trajectory that never reaches 1 contains <code>CFC</code>, <code>CFF</code> and <code>CCC</code> respectively. For other <i>d</i>, “analogue” below always means the statement about parity words, that is, about classes of <i>n</i>/<i>d</i>. Literal residues of <i>n</i> behave differently.

Lean: `Targets.conjecture_4_11_iff`, `conjecture_4_12_iff`, `conjecture_4_13_iff`, `Barrier.class_one`, `class_three`, `class_five`, `class_seven`

## 2. Results

**Definition.**

A word <i>w</i> over {<code>C</code>, <code>F</code>} is <i>forced</i> if for every odd <i>d</i> and every <i>n</i> whose <i>T<sub>d</sub></i>-orbit stays above <i>d</i>, <i>w</i> occurs as a factor of the parity word of that orbit. It is <i>forced over a set D</i> of odd numbers if this holds for all <i>d</i> in <i>D</i>.

**Theorem 1 (descent).**

Let <i>d</i> be odd and <i>n</i> ≥ 1. If no two consecutive terms of the <i>T<sub>d</sub></i>-orbit of <i>n</i> are odd, then some term is at most <i>d</i>. Hence every orbit that stays above <i>d</i> contains <code>CC</code>.

An odd term <i>x</i> followed by an even term gives <i>T<sub>d</sub></i><sup>2</sup>(<i>x</i>) = (3<i>x</i> + <i>d</i>)/4, which is less than <i>x</i> when <i>x</i> &gt; <i>d</i>.

Lean: `Barrier.comes_down`, `Barrier.above_home_climbs_twice`

**Theorem 2 (classification).**

A word is forced if and only if it is empty or one of <code>C</code>, <code>F</code>, <code>CC</code>, <code>CF</code>, <code>FC</code>, <code>CCF</code>, <code>FCC</code>. In particular no word of four or more letters is forced.

The seven follow from Theorem 1 and the fact that no orbit climbs for ever or falls for ever. For the rest, <i>T</i><sub>5</sub> has the cycles 19 → 31 → 49 → 76 → 38 with word <code>CCCFF</code> and 23 → 37 → 58 → 29 → 46 with word <code>CCFCF</code>. Every term exceeds 10. As cyclic words they share no factor of length 4, and every other word of length at most 3 is missing from one of them.

Lean: `Seven.forced_iff`, `Seven.nothing_longer_is_forced`

**Corollary 3 (the conjectures of [1], for 3n + 5).**

For <i>d</i> = 5 there are orbits that stay above <i>d</i> and contain no <code>CFC</code> (the orbit of 19), and neither <code>CFF</code> nor <code>CCC</code> (the orbit of 23). So the parity-word analogues of Conjectures 4.11, 4.12, 4.13, and of the weaker Conjecture 4.14, are all false for <i>T</i><sub>5</sub>.

In the paper’s own terms: its Proposition 4.15 turns Conjecture 4.14 into the convergence of a map <i>H</i>, and among rationals <i>H</i> has the cycle 4/5 → 3/5 → 4/5. By hand: with <i>x</i> = <i>n</i>/5, the odd terms of the first cycle have <i>x</i> ≡ 7, 3, 5 and those of the second have <i>x</i> ≡ 3, 1, 1 modulo 8.

Lean: `Barrier.all_three_fail_in_the_world_of_five`, `Caution.analogue_of_4_14_fails`, `Caution.cycle_of_H`

**Theorem 4 (single maps).**

For each <i>d</i> in {5, 13, 47, 59}, the words forced over {<i>d</i>} are the same eight. These four numbers are pairwise coprime.

Lean: `Seven.four_worlds`

**Theorem 5 (every modulus).**

For every <i>m</i> ≥ 1 and every word <i>w</i> that is not forced, there are an odd <i>d</i> coprime to <i>m</i> and an <i>n</i> whose <i>T<sub>d</sub></i>-orbit stays above <i>d</i> and does not contain <i>w</i>. Equivalently, for every <i>m</i>, the words forced over {<i>d</i> odd : gcd(<i>d</i>, <i>m</i>) = 1} are the same eight.

Lean: `NoModulus.no_modulus_helps`, `NoModulus.forced_modulo`

**Proposition 6 (a related weakening).**

Let <i>d</i> be odd and let <i>M</i> be coprime to <i>d</i> with <i>M</i> = 4 or <i>M</i> ≥ 6. If all but finitely many terms of a <i>T<sub>d</sub></i>-orbit are congruent to <i>d</i> or 2<i>d</i> modulo <i>M</i>, then the orbit reaches <i>d</i>. For <i>M</i> = 5 this fails when <i>d</i> = 13: every term of the 8-cycle through 283 is congruent to 13 or 26 modulo 5. For <i>d</i> = 1 and <i>M</i> = 5 I know no proof. It would follow from Conjecture 4.12, and already from the class 0 statement.

Lean: `Elsewhere.looks_home_is_home`, `Elsewhere.five_is_a_real_exception`, `Barrier.conjecture_412_would_settle_five`

**Proposition 7 (a caution).**

Every <i>T</i><sub>1</sub>-trajectory that never reaches 1 contains some <i>n</i> ≡ 1 (mod 8) or some <i>n</i> ≡ 15 (mod 64); in words, <code>CFC</code> or <code>CCCCFF</code>. Yet for <i>d</i> = 5 the orbit of 19 stays above <i>d</i> and contains neither word.

A trajectory avoiding both moves in blocks of at most three climbs and at least two falls, and each block ends lower: the worst case needs (27<i>n</i> + 19)/32 &lt; <i>n</i>, true for <i>n</i> &gt; 19/5, and an odd integer beginning <code>CCCFF</code> is at least 23. The rational 19/5 is the fixed point of that map. So failing in another <i>T<sub>d</sub></i>, even above <i>d</i>, says nothing by itself about difficulty for 3n + 1. The first sentence is not new: it is the first half of Theorem 8.2(a) of [5, Part II], proved there in Lean, and shown there (Theorem 8.3) to be best possible for certificates of its kind. The weaker form with 15 modulo 16 follows for divergent orbits from [6, Table 2]. Only the second sentence is added here.

Lean: `Caution.one_or_fifteen`, `Caution.next_door`, `Caution.refuted_next_door_and_still_true`

## 3. Proof of Theorem 5, in outline

<b>Every contracting word is realised.</b> Let <i>p</i> be a word of length <i>k</i> with <i>o</i> letters <code>C</code> and 3<sup><i>o</i></sup> &lt; 2<sup><i>k</i></sup>. Put <i>d</i> = 2<sup><i>k</i></sup> − 3<sup><i>o</i></sup> and let <i>c</i>(<i>p</i>) be the sum, over the positions <i>j</i> of the letters <code>C</code>, of 2<sup><i>j</i></sup> 3<sup><i>e</i></sup>, where <i>e</i> counts the letters <code>C</code> after position <i>j</i>. Then <i>c</i>(<i>p</i>) is periodic under <i>T<sub>d</sub></i> with parity word <i>p</i>. This is the classical correspondence [2, 3].

Lean: `Realize.iterate_cOf`, `Realize.pat_cOf`

<b>A test for lying above <i>d</i>.</b> Follow <i>p</i> from the rational starting value 1, applying <i>x</i>/2 or (3<i>x</i> + 1)/2 as the letters prescribe. If every intermediate value is at least 1 and the final value exceeds 1, then every term of the cycle of <i>c</i>(<i>p</i>) exceeds <i>d</i>.

Lean: `Realize.above_home`, `Realize.realize`

<b>Five minimal words.</b> Every word that is not forced contains one of <code>FF</code>, <code>CCC</code>, <code>CFC</code>, <code>FCF</code>, <code>FCCF</code>.

Lean: `NoModulus.contains_minimal`

<b>Two families.</b> The word <code>CCF(CF)<sup>s</sup></code> contains neither <code>FF</code> nor <code>CCC</code>, and <i>d</i> = 2<sup>2<i>s</i>+3</sup> − 3<sup><i>s</i>+2</sup> = 8·4<sup><i>s</i></sup> − 9·3<sup><i>s</i></sup>. The word <code>C<sup>a</sup>FF(CCCFF)<sup>s</sup></code> with <i>a</i> ≥ 3 contains none of <code>CFC</code>, <code>FCF</code>, <code>FCCF</code>, and <i>d</i> = 2<sup><i>a</i>+2+5<i>s</i></sup> − 3<sup><i>a</i>+3<i>s</i></sup>. Take <i>s</i> = <i>m</i>! in the first, and <i>a</i> = 3·<i>m</i>!, <i>s</i> = 3<i>a</i> in the second. By Fermat’s little theorem, for every prime <i>q</i> ≥ 5 dividing <i>m</i> the first <i>d</i> is congruent to 8 − 9 and the second to 4 − 1 modulo <i>q</i>. Both are odd and prime to 3. Both pass the test above.

Lean: `NoModulus.witness_B`, `NoModulus.witness_A`, `NoModulus.coprime_world`

## 4. Relation to the results of [1]

Theorem 4.10 of [1] states that a nonconvergent Collatz trajectory cannot avoid the classes 2, 3, 4, 6 modulo 8. The authors remark that this is not difficult to prove by hand, and their proof of the case 6 is a descent argument. With the even terms 3<i>n</i> + 1 of the <i>C</i>-trajectory included, the dictionary is as follows. The classes 2, 4, 6, 0 are met exactly when <code>CF</code>, <code>FC</code>, <code>CC</code>, <code>FF</code> occur after the first letter. The classes 3, 1, 5, 7 are met exactly when <code>CCF</code>, <code>CFC</code>, <code>CFF</code>, <code>CCC</code> occur anywhere.

So the four proved classes come from forced words, and Theorem 4.10 is re-proved here from those words, for trajectories of <i>C</i> itself. The open classes 0, 1, 7 are the minimal unforced words <code>FF</code>, <code>CFC</code>, <code>CCC</code>. Class 5 is <code>CFF</code>, which contains <code>FF</code>; the statements for 0 and 5 are equivalent, as footnote 12 of [1] notes in one direction.

Lean: `Targets.theorem_4_10`, `Targets.case_zero_of_case_five`

The implications from forced words to classes are formalised; the converse directions of the dictionary are by hand. For single classes modulo 8 the list of forced classes and the list of proved classes coincide. Proposition 7 shows that this is not a general principle. The seven forced words, read as classes for <i>T</i><sub>1</sub>, are 0 and 1 modulo 2, 1 and 2 and 3 modulo 4, and 3 and 6 modulo 8. All seven are listed in [6]: the first four as strongly sufficient (Table 1), the last three as forward sufficient (Table 2). A survey by computer of the primitive cycles reached from starting values up to 4000, for <i>d</i> &lt; 400, found none above <i>d</i> avoiding 2, 3, 4 or 6, and found each of 0, 1, 5, 7 avoided.

The authors also report proofs of the two-class versions {1, 5} and {1, 7}. Both sets are already in the tables of [6]. The first says only that <code>CF</code> occurs. For the second, by hand: avoiding <code>CFC</code> and <code>CCC</code> forces every run of falls to have length at least 2 and every run of climbs at most 2, so each block contracts by at least 9/16 and descent applies. The remaining pair {5, 7}, their Conjecture 4.14, fails for <i>T</i><sub>5</sub> on the cycle through 23.

## 5. What this does and does not show

- <b>It has no bearing on Conjectures 4.11 to 4.14.</b> They concern <i>T</i><sub>1</sub>. For 3n + 1 itself, what is proved here is what descent gives: Theorem 1, the seven forced words, Theorem 4.10 again, and Propositions 6 and 7.
- <b>Forced is sufficient for an easy proof, not necessary.</b> A forced word occurs by an argument that never asks which map it is in. An unforced statement may still be easy for 3n + 1, as Proposition 7 shows: the only fact about 3n + 1 used there is that no odd integer beginning <code>CCCFF</code> is below 3.8.
- <b>Why the open classes resist descent.</b> The reason is visible inside 3n + 1 and is not mine. A trajectory avoiding class 0, 5 or 7 may still take the block <code>CCF</code>, which multiplies by 9/8. One avoiding class 1 may take <code>C<sup>a</sup>FF</code> with <i>a</i> ≥ 4, which multiplies by at least 81/64. These expanding blocks mix freely with contracting ones. Avoiding 2, 3, 4 or 6 leaves only contracting blocks. This is in the proof of Proposition 4.7 of [1] and in the cycle criteria of [6, Propositions 6.2 and 6.5]. Nashida [5] makes it exact. Halt the map on the chosen classes and take its graph on residues modulo a power of 2. The map is <i>entangled</i> if an expanding cycle shares a strongly connected component with a branching vertex. A terminating map of the class studied there has a certificate built from the logarithm, 2-adic valuations at finitely many rational points and finite-state weights if and only if it is not entangled [5, Part I, Corollary B]. The maps of Conjectures 4.11 to 4.14 are entangled [5, Part II, Proposition 8.1]. That paper also determines every single class that can be added to each conjecture so that such a certificate exists [5, Part II, Theorem 8.3]. It notes that no entangled map of this class is known to terminate.
- <b>Where the other maps enter.</b> In [5] an orbit is shown to fall below a bound, and the numbers below the bound are checked directly. In [6] divergent orbits are excluded by the density of odd terms, and cycles by computed facts about 3n + 1: it has no short nontrivial cycle and none with a small element. In Proposition 7 the finite check is the only step that uses the map 3n + 1 rather than 3n + d, and it is what fails for 3n + 5. I believe the same holds for these proofs in general, since <i>T<sub>d</sub></i> is <i>T</i><sub>1</sub> on the rationals <i>n</i>/<i>d</i>, but I have not checked it. So Corollary 3 and Proposition 7 say that 3n + 5 has small cycles, in the language of [1]. They say nothing about the hard part.
- <b>Why “above <i>d</i>”.</b> For <i>d</i> &gt; 1 there can be cycles below <i>d</i>, such as 1 → 4 → 2 for <i>d</i> = 5. These break even the proved statements if read literally, since descent only brings an orbit down to <i>d</i>.
- <b>The reading of Theorem 5 for proof methods is weak.</b> An integer <i>n</i> under <i>T<sub>d</sub></i> is the rational <i>n</i>/<i>d</i> under <i>T</i><sub>1</sub>, which has a residue modulo <i>m</i> exactly when <i>d</i> is prime to <i>m</i>. So Theorem 5 rules out arguments about parities and residues that never use that the terms are integers. Nobody would attempt such an argument, and one small integrality fact can be enough.
- <b>Novelty.</b> That the analogues fail for 3n + 5 would be immediate to anyone who knows [2]. I did not find it in print, and it may never have needed writing down. For 3n + 1 the seven forced classes are in [6] and Proposition 7 is in [5]. What I have not found elsewhere is the statement across all <i>d</i> at once: that exactly these seven survive, for every modulus (Theorems 2, 4 and 5). Neither [5] nor [6] considers the family 3n + d. These are small results. The real question, which weakenings are provable and why the rest are not, is answered for one natural class of proofs in [5].
- <b>Sets of words are open.</b> The pair {<code>FF</code>, <code>FCF</code>} is met by every orbit above <i>d</i> if and only if no orbit, for any <i>d</i>, has at least two climbs between isolated falls for ever. Such an orbit would diverge.

## 6. Machine verification

The proofs are in Lean 4 (toolchain v4.36.0-rc2) with the matching Mathlib release. The project builds with no errors and no <code>sorry</code>, and each theorem named here depends only on the axioms <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. Finite checks on explicit cycles are done by kernel evaluation (<code>decide</code>). Run <code>lake exe cache get</code> and then <code>lake build SevenWords</code> in the root directory of the repository.

| Statement | Lean name | File |
| --- | --- | --- |
| Theorem 1 | <code>above_home_climbs_twice</code> | Barrier.lean |
| Theorem 2 | <code>forced_iff</code> | Seven.lean |
| Corollary 3 | <code>all_three_fail_in_the_world_of_five</code>, <code>analogue_of_4_14_fails</code> | Barrier.lean, Caution.lean |
| Theorem 4 | <code>four_worlds</code> | Seven.lean |
| Theorem 5 | <code>no_modulus_helps</code>, <code>forced_modulo</code> | NoModulus.lean |
| Proposition 6 | <code>looks_home_is_home</code>, <code>five_is_a_real_exception</code> | Elsewhere.lean |
| Proposition 7 | <code>refuted_next_door_and_still_true</code> | Caution.lean |
| Theorem 4.10 of [1], and its conjectures as stated | <code>theorem_4_10</code>, <code>conjecture_4_12_iff</code> | Targets.lean |
| Realisation of words | <code>iterate_cOf</code>, <code>realize</code> | Realize.lean |

Not formalised: the residues quoted under Corollary 3, the converse directions of the dictionary in Section 4, the argument for {1, 7}, the computer survey, and everything in Section 5.

In the Lean files the maps <i>T<sub>d</sub></i> are called worlds, the trivial cycle is called home, and the letters are <code>true</code> for a climb and <code>false</code> for a fall.

The seven files named in the table are copied unchanged, apart from their import lines, from a larger private project. <code>Basics.lean</code> holds the 31 definitions and lemmas they use from the rest of that project, also unchanged (the shortcut map, Terras periodicity, the rational cycle of a parity word). Where a comment in one of the seven files mentions <code>Collatz</code>, <code>Fate</code>, <code>Thread</code> or <code>Bases</code>, it means the part of <code>Basics.lean</code> with that namespace. The comments in the Lean files are written in that vocabulary and in the first person, and include the author's corrections of earlier readings; they are left as they were. The eight files build on their own. As a check independent of Lean, members of both families in Section 3 were also run with ordinary big-integer arithmetic, one of them for a modulus <i>d</i> of more than ten thousand digits. An independent reviewer re-ran these checks and the cycles of Theorems 2 and 4. <code>check_words.py</code> in this directory repeats the finite part with plain integers: the two cycles of <i>T</i><sub>5</sub>, the words they contain, the cycle through 283, small members of both families, and a survey of 187 cycles above <i>d</i> for <i>d</i> &lt; 200.

## 7. A second literature search

Added on 23 November 2026 by a separate search that did not start from the first one's
conclusions. It read [1], [6] and Laarhoven and de Weger [7] in full, and knows Nashida's
preprints [5] only through the descriptions in their public repositories.

- **Theorems 2, 4 and 5.** Not found. The closest statements are for <i>d</i> = 1 only:
  Tables 1 and 2 of [6] contain exactly the seven classes, under the headings "Some strongly
  sufficient sets" and "Some forward sufficient sets", with no claim that the list is complete
  and nothing on 3n + d; and Theorems 4.9 and 4.10 of [1]. That the seven words are forced
  for every <i>d</i> is the same descent argument and should be counted as folklore. The
  converse, that nothing else is forced, was not found stated. [7] restates the
  correspondence between parity words and rational cycles but does not ask which factors
  every cycle must contain.
- **Corollary 3.** Not found stated. It is immediate from cycles that are in standard tables.
  The idea that a cycle elsewhere obstructs these statements is already in [5], which uses
  the cycle of −5 of the 3n + 1 map on negative integers: the terms −5, −7, −10 are 3, 1
  and 6 modulo 8 (checked by hand here), so that cycle avoids the classes 5 and 7.
- **Proposition 6.** Not found, including the exception at <i>M</i> = 5. The mechanism, an
  orbit confined to a loop of the graph on residues is periodic, is used in the proof of
  Proposition 6.2 of [6] for <i>d</i> = 1.

So the assessment in Section 5 stands: the all-<i>d</i> classification appears to be new as
a statement, and it is small. Not finding something is not proof that it is absent.

## 8. References

1. E. Yolcu, S. Aaronson, M. J. H. Heule. An automated approach to the Collatz conjecture. CADE-28 (2021); Journal of Automated Reasoning 67, 15 (2023). [arXiv:2105.14697](https://arxiv.org/abs/2105.14697). Section 4.5 of version 3 was read for this note.
2. J. C. Lagarias. The set of rational cycles for the 3x + 1 problem. Acta Arithmetica 56 (1990), 33–53.
3. C. Böhm, G. Sontacchi. On the existence of cycles of given length in integer sequences like x<sub>n+1</sub> = x<sub>n</sub>/2 if x<sub>n</sub> even, and x<sub>n+1</sub> = 3x<sub>n</sub> + 1 otherwise. Atti Accad. Naz. Lincei 64 (1978), 260–264.
4. OEIS, sequence [A226607](https://oeis.org/A226607): smallest elements of the primitive cycles of the 3x + k maps.
5. H. Nashida. Preprints, Zenodo, 2026. Part I: “Expanding cycles are not enough: a dichotomy for termination certificates of generalized Collatz maps”, revision r3, [doi:10.5281/zenodo.23081447](https://doi.org/10.5281/zenodo.23081447). Part II: “Dimension-free barriers for matrix interpretations of the Collatz rewriting system, and the maximal one-class weakenings of the modulo-8 conjectures of Yolcu, Aaronson and Heule provable by finite abstractions”, revision r3, [doi:10.5281/zenodo.23081491](https://doi.org/10.5281/zenodo.23081491). For this note I read the introductions of both and Section 8 of Part II. A third preprint, on natural-number and arctic interpretations ([doi:10.5281/zenodo.23147025](https://doi.org/10.5281/zenodo.23147025)), I know by its abstract only. The preprints state that they were written with substantial use of AI models and have not yet been checked by independent human experts; their certificates are verified in Lean.
6. K. Monks, K. G. Monks, K. M. Monks, M. Monks. Strongly sufficient sets and the distribution of arithmetic sequences in the 3x + 1 graph. Discrete Mathematics 313 (2013), 468–489. [arXiv:1204.3904](https://arxiv.org/abs/1204.3904). Section 6 of version 2 was read for this note. Not cited in [1]; found through [5].
7. T. Laarhoven, B. de Weger. The Collatz conjecture and De Bruijn graphs. Indagationes Mathematicae 24 (2013), [doi:10.1016/j.indag.2013.03.003](https://doi.org/10.1016/j.indag.2013.03.003). [arXiv:1209.3495](https://arxiv.org/abs/1209.3495).
