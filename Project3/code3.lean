import Mathlib

-- Silence spaces warnings
set_option linter.style.emptyLine false
set_option linter.style.multiGoal true

open Set Filter
open BigOperators

/-!
## Natural and Dirichlet densities in Lean
In this report, we define in Lean the natural and Dirichlet densities of sets of prime numbers.
Let Π be the set of all primes, and let S ⊆ Π. By defining a suitable ratio between the elements of
S and those of Π, we define the natural density of S, denoted by δ(S). We then prove some basic
facts about the natural density.

We then define the Dirichlet density of S, denoted by d(S). Its definition is given in terms of
infinite sums of powers of primes in S and Π. By defining, once again, a suitable ratio,
we prove in detail that these sums converge and hence give rise to a density.

It is important to note that neither the natural density nor the Dirichlet density had
been formalised in Lean before, so this work is a new contribution to the Lean project
and community.

The code follows closely the informal definitions and proofs in the report. In this file we use
headers to organise the results that are needed to prove each lemma in the informal proof.

## Main definitions
- `p` is a prime number.
- `Primes` is the set of all prime numbers.
- `S` is a subset of `Primes`.
- `primesLe` is the set of primes ≤ n ∈ ℕ.
- `primesInSLe` is the set of primes in S ≤ n ∈ ℕ.

## Main results
- We show that the natural density always lies in [0,1].
- We show that δ(Π)=1 and that δ(S)=0 when S is finite.
- We also show that the Dirichlet density always lies in [0,1].

## References
⋆ [Joan Arenillas i Cases, ⋆Euclidean proofs of the infinitude of
   primes in arithmetic progressions⋆, BSc Thesis in Mathematics, June 2025]
-/

/-!
## General definitions
-/

/- Consider a prime p -/
variable (p : ℕ) {hp : Nat.Prime p}

/- Consider a natural number n -/
variable (n : ℕ) {hn : n > 1}

/-- Define the set of all prime numbers -/
def Primes : Set ℕ := {n | Nat.Prime n}

/- Define a subset S of Primes -/
variable (S : Set ℕ) {hS : S ⊆ Primes}

/-- Define the set of primes ≤ n -/
def primesLe (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/-- The set primesLe has cardinality n.primeCounting -/
lemma eq_card_primesLe (n : ℕ) : (primesLe n).card = n.primeCounting := by
  simp only [Nat.primeCounting, primesLe, Nat.primeCounting']
  simp [Nat.count_eq_card_filter_range]

/-- Define the set of primes in S ≤ n -/
noncomputable def primesInSLe (S : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun p ↦ Nat.Prime p ∧ p ∈ S)

/-- Define the ratio (# {p ∈ S, p ≤ n}) / (# {p prime, p ≤ n}) as a real number -/
noncomputable def densityRatio (S : Set ℕ) (n : ℕ) : ℝ :=
  (primesInSLe S n).card / n.primeCounting

/-- The natural number # {p ∈ S, p ≤ n} is non-negative -/
lemma cardinality_primesInSLe_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ (primesInSLe S n).card := by
  rw [primesInSLe]; grind

/-- The natural number # {p prime, p ≤ n} is positive -/
lemma cardinality_primesLe_pos (n : ℕ) (hn : 1 < n) : 0 < (primesLe n).card := by
  rw [primesLe]
  -- The set primesLe is non-empty
  have h_nonempty : (Finset.filter Nat.Prime (Finset.range (n + 1))).Nonempty := by
    use 2
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · grind
    · norm_num
  exact Finset.card_pos.mpr h_nonempty -- obtained with `exact?`

/-- The ratio (# {p ∈ S, p ≤ n}) / (# {p prime, p ≤ n}) is non-negative -/
lemma densityRatio_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ densityRatio S n := by
  rw [densityRatio]; positivity

/-- The ratio (# {p ∈ S, p ≤ n}) / (# {p prime, p ≤ n}) is smaller than or equal to 1 -/
lemma densityRatio_leq_one (S : Set ℕ) (n : ℕ) : (densityRatio S n) ≤ 1 := by
  rw [densityRatio]
  -- primesInSLe is a subset of primesLe
  have h: primesInSLe S n ⊆ primesLe n := by
    intro p hp
    simp only [primesLe, Finset.mem_filter, Finset.mem_range] at hp ⊢
    simp only [primesInSLe, Finset.mem_filter, Finset.mem_range] at hp
    constructor
    · exact hp.1
    · exact hp.2.1
  have h_card : ↑(primesLe n).card = ↑n.primeCounting := by
    exact eq_card_primesLe n
  -- primesInSLe has less elements than primesLe
  have h_le : ((primesInSLe S n).card : ℝ) ≤ n.primeCounting := by
    have h_card_subset : ↑((primesInSLe S n).card : ℝ) ≤ ↑(primesLe n).card := by
      exact_mod_cast Finset.card_le_card h
    exact le_of_le_of_eq h_card_subset (congrArg Nat.cast h_card) -- obtained with `exact?`
  have h_pos : (0 : ℝ) ≤ ↑n.primeCounting := by
    exact Nat.cast_nonneg' n.primeCounting -- obtained with `exact?`
  exact div_le_one_of_le₀ h_le h_pos

/-- Define the upper natural density of S in Primes -/
noncomputable def upperNaturalDensityInPrimes (S : Set ℕ) : ℝ :=
  Filter.limsup (densityRatio S) Filter.atTop

/-- Define the lower natural density of S in Primes -/
noncomputable def lowerNaturalDensityInPrimes (S : Set ℕ) : ℝ :=
  Filter.liminf (densityRatio S) Filter.atTop

/-- Define the natural (or asymptotic) density of S in Primes -/
noncomputable def NaturalDensityInPrimes (S : Set ℕ) : ℝ :=
  if lowerNaturalDensityInPrimes S = upperNaturalDensityInPrimes S
    then upperNaturalDensityInPrimes S
  else 0

-- Note: atTop is a filter on ℕ meaning "for sufficiently large n, the statement holds"
-- Note: Could have also defined the natural density through the lower density

/-!
## Facts about the natural density
-/

/-- The natural density is non-negative -/
lemma natural_density_nonneg (S : Set ℕ)
    (hd : lowerNaturalDensityInPrimes S = upperNaturalDensityInPrimes S) :
    0 ≤ NaturalDensityInPrimes S := by
  rw [NaturalDensityInPrimes, hd, upperNaturalDensityInPrimes]
  simp only [↓reduceIte]
  -- If every element of a set is nonnegative, then its infimum is nonnegative
  refine Real.sInf_nonneg ?_
  intro x hx
  -- Write hx in a nicer way
  change ∀ᶠ y in Filter.map (densityRatio S) Filter.atTop, y ≤ x at hx
  change ∀ᶠ n in Filter.atTop, densityRatio S n ≤ x at hx
  -- Unpack the eventually_atTop filter
  rcases Filter.eventually_atTop.mp hx with ⟨m, hm⟩
  exact le_trans (densityRatio_nonneg S m) (hm m le_rfl)

/-- The natural density is at most 1 -/
lemma natural_density_leq_one (S : Set ℕ)
    (hd : lowerNaturalDensityInPrimes S = upperNaturalDensityInPrimes S) :
    NaturalDensityInPrimes S ≤ 1 := by
  rw [NaturalDensityInPrimes, hd]
  simp only [↓reduceIte]
  rw [upperNaturalDensityInPrimes]
  have densityRatio_leq_one : ∀ n, n > 1 → densityRatio S n ≤ 1 := by
    intro n hn
    exact densityRatio_leq_one S n
  refine' csInf_le _ _ -- leaves the two assumptions as goals
  all_goals norm_num -- try norm_num in all goals
  · refine ⟨0, ?_⟩ -- 0 is an eventual upper bound
    rintro x ⟨N, hN⟩
    have h_bound : densityRatio S N ≤ x := by
      exact hN N le_rfl
    have h_nonneg : 0 ≤ densityRatio S N := by
      exact densityRatio_nonneg S N
    exact le_trans h_nonneg h_bound
  · refine ⟨2, ?_⟩ -- from n = 2 the ratio is at most 1
    intro n hn
    exact densityRatio_leq_one n hn

/-- The set Primes has natural density 1 -/
lemma natural_density_Primes : NaturalDensityInPrimes Primes = 1 := by
  -- The densityRatio with S = Π is = 1 for all n > 1
  have h_dens : ∀ n, n > 1 → densityRatio Primes n = 1 := by
    intro n hn
    rw [densityRatio]
    -- Set S = Π in the definition of primesInSLe
    have h_eq : primesInSLe Primes n = primesLe n := by
      -- Double inclusion
      apply Finset.Subset.antisymm
      · intro hmem
        simp only [primesInSLe, Finset.mem_filter, Finset.mem_range, primesLe, and_imp] at hmem ⊢
        exact fun a a_1 a_2 ↦ And.symm ⟨a_1, a⟩ -- obtained with `apply?`
      · intro hmem
        simp only [primesLe, Finset.mem_filter, Finset.mem_range, primesInSLe, and_imp] at hmem ⊢
        aesop
    -- The set primesLe has the same elements as primeCounting
    have h_card : (primesLe n).card = n.primeCounting := by
      exact eq_card_primesLe n
    simp only [h_eq, h_card]
    -- primeCounting is positive
    have pos : (0 : ℝ) < n.primeCounting := by
      have hprime : Nat.Prime 2 := by decide
      have hmem : 2 ∈ (primesLe n) := by
        simp only [primesLe, Finset.mem_filter, Finset.mem_range]
        constructor
        · grind
        · norm_num
      have h_card_pos : (primesLe n).card > 0 := by grind
      exact_mod_cast (by simpa [eq_card_primesLe n] using h_card_pos)
    grind
  -- Lower natural density is 1
  have h_lower : lowerNaturalDensityInPrimes Primes = 1 := by
    rw [lowerNaturalDensityInPrimes]
    -- eventually, for all sufficiently large n, densityRatio Primes n = 1
    have h_eventually : ∀ᶠ n in atTop, densityRatio Primes n = 1 := by
      -- eventually_gt_atTop gives n and hn
      filter_upwards [eventually_gt_atTop 1] with n hn
      exact h_dens n hn
    rw [liminf_congr h_eventually]
    simp
  -- Upper natural density is 1
  have h_upper : upperNaturalDensityInPrimes Primes = 1 := by
    rw [upperNaturalDensityInPrimes]
    have h_eventually : ∀ᶠ n in atTop, densityRatio Primes n = 1 := by
      filter_upwards [eventually_gt_atTop 1] with n hn
      exact h_dens n hn
    rw [limsup_congr h_eventually]
    simp
  -- Lower density = Upper density
  have h_equal : lowerNaturalDensityInPrimes Primes = upperNaturalDensityInPrimes Primes := by
    rw [h_lower, h_upper]
  rw [NaturalDensityInPrimes, h_equal]
  simp only [↓reduceIte]
  exact h_upper

/-- If S is finite, its natural density is 0 -/
lemma natural_density_finite_eq_zero (S : Set ℕ) (hS : S.Finite)
    (hd : lowerNaturalDensityInPrimes S = upperNaturalDensityInPrimes S) :
    NaturalDensityInPrimes S = 0 := by
  -- primesInSLe is a subset of S
  have h_subset : ∀ n, primesInSLe S n ⊆ hS.toFinset := by
    intro n p hp
    have hp' : p ∈ Finset.range (n + 1) ∧ Nat.Prime p ∧ p ∈ S := by
      simpa [primesInSLe] using hp
    have hpS : p ∈ S := hp'.2.2
    exact (Finite.mem_toFinset hS).mpr hpS -- obtained with `apply?`
  -- The numerator is bounded by the (finite) cardinality of S
  have h_num_bdd : ∀ n, (primesInSLe S n).card ≤ hS.toFinset.card := by
    intro n
    exact Finset.card_le_card (h_subset n)
  -- The denominator tends to ∞ as n → ∞
  have h_lim_den : Tendsto (fun (n : ℕ) => n.primeCounting) atTop atTop := by
    exact Nat.tendsto_primeCounting
  set M : ℕ := hS.toFinset.card
  rw [NaturalDensityInPrimes, hd]
  simp only [↓reduceIte]
  rw [upperNaturalDensityInPrimes]
  -- Since the ratio tends to zero, the upper natural density must also be zero
  have h_upper_zero :
      Filter.limsup (fun n => ((primesInSLe S n).card : ℝ) / (Nat.primeCounting n))
      Filter.atTop = 0 := by
    refine' Filter.Tendsto.limsup_eq _
    refine' squeeze_zero_norm' _ _ -- see report for explanation
    · use fun n => M / Nat.primeCounting n
    · filter_upwards [h_lim_den.eventually_gt_atTop 0] with n hn
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      exact_mod_cast h_num_bdd n
    · -- A constant divided by something going to ∞ is 0
      exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h_lim_den)
  convert h_upper_zero -- reduce the goal to proving an equality of functions

/-!
## Dirichlet density for sets of prime numbers
-/

/-- Define the real number ∑(p ∈ S) p^{-s} -/
noncomputable def sum_top (S : Set ℕ) [DecidablePred (· ∈ S)] (s : ℝ) : ℝ :=
  ∑' p : ℕ, if p ∈ S then (p : ℝ) ^ (-s) else 0

/-- Define the real number ∑(p ∈ Prime) p^{-s} -/
noncomputable def sum_bott [DecidablePred (· ∈ Primes)] (s : ℝ) : ℝ :=
  ∑' p : ℕ, if p ∈ Primes then (p : ℝ) ^ (-s) else 0

/-- Define the real number (∑(p ∈ S) p^{-s}) / (∑(p ∈ Prime) p^{-s}) -/
noncomputable def densityRatio_Dirichlet (S : Set ℕ) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Primes)] (s : ℝ) : ℝ :=
  (sum_top S s) / (sum_bott s)

/-- p^(-s) is positive for all s ∈ ℝ -/
lemma p_minus_s_pos (s : ℝ) : ∀ p ∈ Primes, (p : ℝ) ^ (-s) > 0 := by
  intro p hp
  rw [Primes] at hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp_pos : 0 < (p : ℝ) := by grind
  exact Real.rpow_pos_of_pos hp_pos (-s) -- obtained with `exact?`

/-- The sum ∑(p ∈ Primes) p^{-s} converges -/
lemma h_den_summable [DecidablePred (· ∈ Primes)] (s : ℝ) (hs : 1 < s) :
    Summable (fun p : ℕ => if p ∈ Primes then (p : ℝ) ^ (-s) else 0) := by
  -- ∑_p ∈ ℕ p^{-s} converges
  have h_subset_summable : Summable (fun p : ℕ => (p : ℝ) ^ (-s)) := by
    apply Real.summable_nat_rpow.mpr; linarith
  have h_pos : ∀ p ∈ Primes, (p : ℝ) ^ (-s) > 0 := by
    exact fun p a ↦ p_minus_s_pos s p a
  -- ∑_p ∈ Primes p^{-s} converges
  apply Summable.of_nonneg_of_le _ _ h_subset_summable -- comparison test of convergence
    -- Break into easier goals
  · intro b
    by_cases h : b ∈ Primes
    · rw [if_pos h]
      exact (h_pos b h).le
    · rw [if_neg h]
  · intro b
    by_cases h : b ∈ Primes
    · rw [if_pos h]
    · rw [if_neg h]
      refine Real.rpow_nonneg ?_ (-s) -- obtained with `apply?`
      exact Nat.cast_nonneg' b -- obtained with `apply?``

/-- The sum ∑(p ∈ S) p^{-s} converges -/
lemma h_num_summable (S : Set ℕ) (hS : S ⊆ Primes) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Primes)] (s : ℝ) (hs : 1 < s) :
    Summable (fun p : ℕ => if p ∈ S then (p : ℝ) ^ (-s) else 0) := by
  have h_sum : Summable (fun p : ℕ => if p ∈ Primes then (p : ℝ) ^ (-s) else 0) := by
    apply h_den_summable s hs
  -- Since S is a subset Primes, we can apply the
  -- comparison test with the known summable series over all primes
  have h_comparison : ∀ p : ℕ, (if p ∈ S then (p : ℝ) ^ (-s) else 0)
      ≤ (if p ∈ Primes then (p : ℝ) ^ (-s) else 0) := by
    intros p
    by_cases hp : p ∈ S
    · -- Case p ∈ S: p ∈ Primes, and thus the inequality holds
      simp [hp, hS hp]
    · -- Case p ∉ S
      by_cases hp' : p ∈ Primes
      · simp [hp, hp']
        positivity
      · simp [hp, hp']
  exact Summable.of_nonneg_of_le -- comparison test
    (fun p => by positivity)
    h_comparison
    h_sum

/-- The real number ∑(p ∈ S) p^{-s} is non-negative -/
lemma sum_top_nonneg (S : Set ℕ) [DecidablePred (· ∈ S)] (s : ℝ) : 0 ≤ sum_top S s := by
  rw [sum_top]; positivity

/-- The sum ∑(p ∈ Prime) p^{-s} is positive -/
lemma sum_bot_pos [DecidablePred (· ∈ Primes)] (s : ℝ) (hs : 1 < s)
    : 0 < sum_bott s := by
  -- p^(-s) is positive
  have h_pos : ∀ p ∈ Primes, (p : ℝ) ^ (-s) > 0 := by
    exact fun p a ↦ p_minus_s_pos s p a
  -- ∑_p ∈ Primes p^{-s} converges
  have h_sum : Summable (fun p : ℕ ↦ if p ∈ Primes then (p : ℝ) ^ (-s) else 0) := by
    exact h_den_summable s hs
  -- One term of the sum is smaller than the whole sum
  have h_bound : (2 : ℝ)^(-s) ≤ (∑' (p : ℕ), if p ∈ Primes then (p : ℝ)^(-s) else 0) := by
    set f : ℕ → ℝ := fun p => if p ∈ Primes then (p : ℝ)^(-s) else 0
    have h2 : f 2 ≤ ∑' (i : ℕ), f i := by
      have h_nonneg : ∀ p, 0 ≤ f p := by
        intro p
        by_cases h : p ∈ Primes
        · simp only [h, ↓reduceIte, f]
          exact (h_pos p h).le
        · positivity
      have h := Summable.sum_le_tsum (s := ({2} : Finset ℕ))
        (by
          intro a ha
          exact h_nonneg a)
          h_sum
      simpa [ge_iff_le, Finset.sum_singleton] using h
    have h2p : 2 ∈ Primes := by
      simp only [Primes, mem_setOf_eq]; norm_num
    simpa [f, h2p] using h2
  -- 2^(-s) is positive
  have h_pos : 0 < (2 : ℝ)^(-s) := by
    refine Real.rpow_pos_of_pos ?_ (-s); norm_num
  -- Combine inequalities
  exact Std.lt_of_lt_of_le h_pos h_bound -- obtained with `exact?`

/-- The ratio (∑(p ∈ S) p^{-s}) / (∑(p ∈ Prime) p^{-s}) is non-negative -/
lemma densityRatio_Dirichlet_nonneg (S : Set ℕ) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Primes)]
    (s : ℝ) (hs : 1 < s) : 0 ≤ densityRatio_Dirichlet S s := by
  rw [densityRatio_Dirichlet]
  -- Bound numerator
  have h_num_nonneg : 0 ≤ sum_top S s := by
    exact sum_top_nonneg S s
  -- Bound denominator
  have h_den_pos : 0 < sum_bott s := by
    exact sum_bot_pos s hs
  positivity

/-- The ratio (∑(p ∈ S) p^{-s}) / (∑(p ∈ Prime) p^{-s}) is smaller than or equal to 1 -/
lemma densityRatio_Dirichlet_leq_one (S : Set ℕ) (hS : S ⊆ Primes)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Primes)]
    (s : ℝ) (hs : 1 < s) : (densityRatio_Dirichlet S s) ≤ 1 := by
  rw [densityRatio_Dirichlet]
  -- ∑(p ∈ Prime) p^{-s} is positive
  have h_den_pos : 0 < sum_bott s := by
    exact sum_bot_pos s hs
  -- p^(-s) is positive
  have h_pos : ∀ p ∈ Primes, (p : ℝ) ^ (-s) > 0 := by
    exact fun p a ↦ p_minus_s_pos s p a
  -- Prove that the numerator is greater than or equal to the denominator
  have h_bound : sum_top S s ≤ sum_bott s := by
    rw [sum_top, sum_bott]
    set f : ℕ → ℝ := fun p => if p ∈ S then (p : ℝ)^(-s) else 0
    simp only [f]
    -- Use the fact that S ⊆ Primes and that all the terms are positive
    have h_pointwise : ∀ p : ℕ, (if p ∈ S then (p : ℝ) ^ (-s) else 0) ≤
        if p ∈ Primes then (p : ℝ) ^ (-s) else 0 := by
      intro p
      by_cases hpS : p ∈ S
      · have hpP : p ∈ Primes := hS hpS
        simp only [hpS, ↓reduceIte, hpP, le_refl]
      · by_cases hpP : p ∈ Primes
        · simp only [hpS, ↓reduceIte, hpP]
          exact Std.le_of_lt (h_pos p hpP) -- obtained with `exact?`
        · simp only [hpS, ↓reduceIte, hpP, le_refl]
    -- Use that the sums converge
    have h_num := h_num_summable S hS s hs
    have h_den := h_den_summable s hs
    -- Prove sum inequality
    exact Summable.tsum_mono h_num h_den h_pointwise -- obtained with `exact?`
  exact (div_le_one₀ h_den_pos).mpr h_bound -- obtained with `exact?`

/-- Define the upper Dirichlet density of S -/
noncomputable def upperDirichletDensity (S : Set ℕ) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Primes)] : ℝ :=
  Filter.limsup (fun s => densityRatio_Dirichlet S s) (nhdsWithin 1 (Set.Ioi 1))

/-- Define the lower Dirichlet density of S -/
noncomputable def lowerDirichletDensity (S : Set ℕ) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Primes)] : ℝ :=
  Filter.liminf (fun s => densityRatio_Dirichlet S s) (nhdsWithin 1 (Set.Ioi 1))

/-- Define the Dirichlet (or analytic) density of S -/
noncomputable def Dirichlet_density (S : Set ℕ) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Primes)] : ℝ :=
  if upperDirichletDensity S = lowerDirichletDensity S
    then upperDirichletDensity S
  else 0

-- Note: Could have also defined the Dirichlet density through the lower density

/-- Dirichlet density is non-negative -/
lemma Dirichlet_dens_nonneg (S : Set ℕ) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Primes)]
    (hd : upperDirichletDensity S = lowerDirichletDensity S) :
    0 ≤ Dirichlet_density S := by
  -- Upper Dirichlet density is nonnegative
  have h_upper_nonneg : 0 ≤ upperDirichletDensity S := by
  -- If every element of a set is nonnegative, then its infimum is nonnegative
    refine Real.sInf_nonneg ?_
    -- Take an arbitrary eventual upper bound `a`, and prove `0 ≤ a`
    intro a ha
    -- Eventually, along the mapped filter, the values are at most `a`
    change ∀ᶠ n in Filter.map (fun s ↦ densityRatio_Dirichlet S s)
      (nhdsWithin 1 (Set.Ioi 1)), n ≤ a at ha
    -- For s sufficiently close to 1 from the right, `densityRatio_Dirichlet S s ≤ a`
    change ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), densityRatio_Dirichlet S s ≤ a at ha
    -- Eventually, s will satisfy 1 < s < 2
    have h_mem : Set.Ioo (1 : ℝ) 2 ∈ nhdsWithin 1 (Set.Ioi 1) := by
      exact Ioo_mem_nhdsGT_of_mem ⟨le_rfl, by norm_num⟩
    -- Eventually, the ratio is at most `a` and 1 < s < 2
    have h_event : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
        densityRatio_Dirichlet S s ≤ a ∧ s ∈ Set.Ioo (1 : ℝ) 2 := by
      exact ha.and h_mem
    -- Get some s for which `h_event` is true
    rcases h_event.exists with ⟨s, hs⟩
    -- Combine inequalities to prove 0 ≤ a
    exact le_trans (densityRatio_Dirichlet_nonneg S s hs.2.1) hs.1
  unfold Dirichlet_density -- unfold definition in the goal
  simp [hd]
  -- Combine inequalities
  exact le_of_le_of_eq h_upper_nonneg hd -- obtained with `exact?`

/-- Dirichlet density is at most 1 -/
lemma Dirichlet_dens_leq_one (S : Set ℕ) (hS : S ⊆ Primes)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Primes)]
    (hd : upperDirichletDensity S = lowerDirichletDensity S) :
    Dirichlet_density S ≤ 1 := by
  unfold Dirichlet_density
  simp [hd]
  rw [← hd]
  refine Filter.limsup_le_of_le ?_ ?_ -- this theorem gives 2 subgoals (see report)
  · exact Filter.isCoboundedUnder_le_of_eventually_le _ (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact densityRatio_Dirichlet_nonneg S s hs)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact densityRatio_Dirichlet_leq_one S hS s hs

--- Run lint at the end to check for (formatting) errors
#lint
