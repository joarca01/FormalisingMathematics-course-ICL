import Mathlib

-- Silence spaces warnings
set_option linter.style.emptyLine false
set_option linter.style.multiGoal true

open Set
open IntermediateField IsGalois Polynomial

/-!
## An explicit Galois extension of ℚ
This file defines a finite, explicit field extension over the field ℚ. We begin by defining
some algebraic elements α and β in terms of a primer number p, and considering the minimal
polynomial of α and β. We then prove that Q(α) ≅ Q(β) and that, in fact, they correspond to
the same subfield of ℂ if √p−1 belongs to ℚ.

Moreover, we generally prove that ℚ(α,β)/ℚ is a Galois extension and we determine its
Galois group to be isomorphic to is ℤ/4ℤ. Finally, we could use the fundamental theorem
of Galois theory to deduce that the only non-trivial subfield lying between ℚ(α,β) and
ℚ is ℚ(√p) (not implemented).

The code follows closely the informal proof. In this file we use headers to organise the results
that are needed to prove each lemma in the informal proof.

## Main definitions
- `p` is a prime number.
- `α` is defiend to be √(p+√p).
- `β` is defiend to be √(p-√p).
- `m_alpha` is the minimal polynomial of α (and β).
- `Q_a` is the field extension ℚ(α).
- `Q_b` is the field extension ℚ(β).
- `Q_ab` is the field extension ℚ(α,β), which turns out to be equal to ℚ(α).
- `Gal_Q_ab` is the Galois group of the extension ℚ(α,β) over ℚ.

## Main result
We prove that if p is a prime, α := √(p+√p), and β := √(p-√p), then Gal(ℚ(α,β)/ℚ) ≅ ℤ/4ℤ.

## References
⋆ [Xavier Xarles, ⋆Notes on Galois Theory⋆, Autonomous University of Barcelona, 2024]
-/

/-!
## General definitions
-/
/- We consider a prime p. -/
variable (p : ℕ) (hp : Nat.Prime p)

/-- Define α in terms of p. -/
noncomputable def α : ℝ := Real.sqrt ((p : ℝ) + Real.sqrt (p : ℝ))

/-- Define β in terms of p. -/
noncomputable def β : ℝ := Real.sqrt ((p : ℝ) - Real.sqrt (p : ℝ))

/-- Define a polynomial m_alpha with coefficients in ℚ. -/
noncomputable def m_alpha (p : ℕ) : Polynomial ℚ := X^4 - C (2 * p : ℚ) * X^2 + C (p*(p-1) : ℚ)

/-!
## Lemmas to prove Lemma 2
-/
/-- Prove that √↑p ≤ ↑p -/
lemma ineq_sqrtp (p : ℕ) (hp : Nat.Prime p) : √↑p ≤ ↑p := by
  have h0 : 0 ≤ (p : ℝ) := by positivity
  have h1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsub : (p : ℝ) ≤ p^2 := by
    have := lt_mul_self h1
    simpa only [pow_two, ge_iff_le] using le_of_lt this
  apply Real.sqrt_le_iff.mpr ⟨h0, hsub⟩

/-- α is a root of m_alpha -/
lemma eval_alpha_zero : aeval (α p) (m_alpha p) = 0 := by
  simp only [α, m_alpha, map_mul, map_natCast, map_sub, map_one, map_add, map_pow,
    aeval_X, aeval_C, eq_ratCast, Rat.cast_ofNat] -- Suggested by `simp?`
  have pos : 0 ≤ ↑p + √↑p := by positivity
  rw [show (4 : ℕ) = 2 + 2 by decide, pow_add, Real.sq_sqrt]
  · ring_nf; rw [Real.sq_sqrt] -- Nice way to write two tactics in one line
    · linarith
    · positivity
  · exact pos

/-- β is a root of m_alpha -/
lemma eval_beta_zero (hp : Nat.Prime p) : aeval (β p) (m_alpha p) = 0 := by
  simp only [β, m_alpha, map_mul, map_natCast, map_sub, map_one, map_add, map_pow,
    aeval_X, aeval_C, eq_ratCast, Rat.cast_ofNat] -- Suggested by `simp?`
  rw [show (4 : ℕ) = 2 + 2 by decide, pow_add, Real.sq_sqrt]
  · ring_nf
    rw [Real.sq_sqrt]
    · ring_nf
    · positivity
  · linarith [ineq_sqrtp p hp]

/-- m_alpha is of degree 4 -/
lemma m_alpha_degree_4 : (m_alpha p).natDegree = 4 := by
  simp only [m_alpha]
  compute_degree <;> norm_num
-- `<;>` uses norm_num in every subgoal produced by compute_degree (shown by a TA)

/-- m_alpha is monic -/
lemma m_alpha_monic : Monic (m_alpha p) := by
  rw [Monic, leadingCoeff, m_alpha_degree_4]
  simp only [m_alpha, map_mul, map_natCast, mul_assoc, map_sub, map_one, coeff_add, coeff_sub,
    coeff_X_pow, ↓reduceIte, coeff_C_mul, coeff_natCast_mul, Nat.reduceEqDiff, mul_zero, sub_zero,
    coeff_natCast_ite, OfNat.ofNat_ne_zero, CharP.cast_eq_zero, coeff_one, sub_self, add_zero]
    -- Suggested by `simp?`

/-- To use Eisenstein's criterion we need m_alpha to live in ℤ[X] -/
noncomputable def m_alpha_Z (p : ℕ) : Polynomial ℤ := X^4 - C (2 * p : ℤ) * X^2 + C (p*(p-1) : ℤ)

/-- m_alpha_Z is of degree 4 -/
lemma m_alpha_Z_degree_4 : (m_alpha_Z p).natDegree = 4 := by
  simp only [m_alpha_Z]
  compute_degree <;> norm_num

/-- m_alpha_Z is monic -/
lemma m_alpha_monic_Z : Monic (m_alpha_Z p) := by
  rw [Monic, leadingCoeff, m_alpha_Z_degree_4]
  simp only [m_alpha_Z, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, mul_assoc,
    Int.cast_sub, Int.cast_one, coeff_add, coeff_sub, coeff_X_pow, ↓reduceIte, coeff_ofNat_mul,
    coeff_natCast_mul, Nat.reduceEqDiff, mul_zero, sub_zero, coeff_natCast_ite, OfNat.ofNat_ne_zero,
    CharP.cast_eq_zero, coeff_one, sub_self, add_zero]
    -- Suggested by `simp?`

/- I have extensively used the `simp?` tactic to avoid simp statements
as suggested in the lectures. From now on, I will omit the "Suggested by `simp?`"
comment for readability, but it should be assumed I used it when long `simp only [...]`
blocks are displayed -/

/-- m_alpha is irreducible in ℤ[X] via Eisentstein at (p) -/
lemma m_alpha_Z_irreducible (hp : Nat.Prime p) : Irreducible (m_alpha_Z p) := by
  -- Define the prime ideal 𝓟 := (p)
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  apply Polynomial.irreducible_of_eisenstein_criterion (P := P) -- Encodes Eisenstein criterion

  · -- (p) is prime
    refine (Ideal.span_singleton_prime ?_).mpr ?_ -- Suggested by `apply?`
    · refine Int.ofNat_ne_zero.mpr ?_
      exact hp.ne_zero
    · exact Nat.prime_iff_prime_int.mp hp

  · -- Leading coeff of m_alpha not in (p)
    simp only [m_alpha_Z, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_sub,
      Int.cast_one, P]
    refine Monic.leadingCoeff_notMem ?_ ?_ -- Suggested by `apply?`
    · simpa only [m_alpha_Z, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_sub, Int.cast_one] using m_alpha_monic_Z p
    · refine Ideal.span_singleton_ne_top ?_ -- Suggested by `apply?`
      refine Irreducible.not_isUnit ?_ -- Suggested by `apply?`
      have hpZ : Prime (p : ℤ) := by exact Nat.prime_iff_prime_int.mp hp
      exact hpZ.irreducible

  · -- All non-leading coeffs of m_alpha in (p)
    intro n hn
    have hn4 : n < 4 := by simpa only [coe_lt_degree, m_alpha_Z_degree_4] using hn
    refine Ideal.mem_span_singleton.mpr ?_ -- Suggested by `apply?`
    have hnle : n ≤ 3 := Nat.lt_succ_iff.mp hn4
    -- Do cases on the coefficient index
    interval_cases n
    · simp [m_alpha_Z]
    · simp [m_alpha_Z]
      refine (Int.dvd_add_right ?_).mpr ?_ -- Suggested by `apply?`
      · (simp only [dvd_neg]; ring_nf)
        simp only [coeff_mul_ofNat, coeff_natCast_mul, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte,
          mul_zero, zero_mul, dvd_zero]
      · (simp only [dvd_neg]; aesop)
    · simp [m_alpha_Z]
      refine (Int.dvd_add_right ?_).mpr ?_
      · (simp only [dvd_neg]; ring_nf)
        (simp only [coeff_mul_ofNat, coeff_natCast_mul, coeff_X_pow, ↓reduceIte]; ring_nf)
        simp only [dvd_mul_right]
      · (simp only [dvd_neg]; aesop)
    · simp [m_alpha_Z]
      refine (Int.dvd_add_right ?_).mpr ?_
      · (simp only [dvd_neg]; ring_nf)
        simp only [coeff_mul_ofNat, coeff_natCast_mul, coeff_X_pow, OfNat.ofNat_eq_ofNat,
          Nat.succ_ne_self, ↓reduceIte, mul_zero, zero_mul, dvd_zero]
      · (simp only [dvd_neg]; aesop)

  · -- Degree of m_alpha > 0
    refine natDegree_pos_iff_degree_pos.mp ?_ -- Suggested by `apply?`
    rw [m_alpha_Z_degree_4]; norm_num

  · -- Constant coefficient of m_alpha not in (p)^2
    simp only [pow_two, m_alpha_Z, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_sub, Int.cast_one, coeff_add, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat,
      ↓reduceIte, mul_coeff_zero, coeff_ofNat_mul, coeff_natCast_ite, coeff_X_zero, mul_zero,
      sub_self, coeff_one_zero, zero_add, P]
    intro h
    have h1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
    have h3 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    -- Reduce it to a computation in ℤ
    have hdiv : (↑p^2 : ℤ) ∣ (↑p * (↑p - 1)) := by
      have h' : (↑p : ℤ) * ((↑p : ℤ) - 1) ∈ Ideal.span {(↑p : ℤ)^2} := by
        simpa [Ideal.span_singleton_mul_span_singleton,
           pow_two, mul_comm, mul_left_comm, mul_assoc]
        using h
      simpa [Ideal.mem_span_singleton] using h'
    have h21 : (↑p : ℤ) * (↑p : ℤ) ∣ (↑p : ℤ) * ((↑p : ℤ) - 1) := by
      rw [pow_two] at hdiv
      exact hdiv
    have h23 : (↑p : ℤ) ∣ ((↑p : ℤ) - 1) :=
      (mul_dvd_mul_iff_left h3).1 (by simpa using h21)
    simp at h23
    norm_cast at h23; simp at h23
    norm_cast at h1
    grind

  · -- m_alpha_Z is primitive
    refine Monic.isPrimitive ?_ -- Suggested by `apply?`
    simpa only [m_alpha_Z, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_sub,
      Int.cast_one] using m_alpha_monic_Z p

/-- Lift of m_alpha_Z to ℚ is m_alpha -/
lemma map_m_alpha_Z : map (Int.castRingHom ℚ) (m_alpha_Z p) = m_alpha p := by
  aesop (add simp [m_alpha_Z, m_alpha])

/-- m_alpha is irreducible in ℚ[X]: Lift irreducibility to ℚ[X] using Gauss’s lemma --/
@[grind .]
lemma m_alpha_irreducible (hp : Nat.Prime p) : Irreducible (m_alpha p) := by
  have hprim : IsPrimitive (m_alpha_Z p) := (m_alpha_monic_Z p).isPrimitive
  have hmap := map_m_alpha_Z p
  have hQ : Irreducible ((m_alpha_Z p).map (Int.castRingHom ℚ)) :=
    -- Use the theorem Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (LeanSearch)
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
      (m_alpha_Z_irreducible p hp)
  simpa only [hmap] using hQ

/-- m_alpha is the minimal polynomial of α over ℚ -/
@[grind =] -- it means, when you see the LHS, write the RHS.
-- `@[grind =_]` is the other way around.
-- `@[grind _=_]` means either of the previous two.
-- `@[grind .]` applies the whole equality.
-- `@[grind →]` operates in implications (same for `@[grind ←]`).
lemma min_pol_alph (hp : Nat.Prime p) : minpoly ℚ (α p) = m_alpha p := by
  refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_) -- Suggested by `apply?`
  -- We use the previous lemmas
  · grind
  · apply eval_alpha_zero
  · apply m_alpha_monic p

/-- The minimal polynomial of β is the same as that of α. -/
@[grind =]
lemma min_pol_beta (hp : Nat.Prime p) : minpoly ℚ (β p) = m_alpha p := by
  refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_)
  -- We use the previous lemmas
  · apply m_alpha_irreducible p hp
  · apply eval_beta_zero p hp
  · apply m_alpha_monic p

/-- The minimal polynomials of α and β are the same -/
lemma min_pol_beta_alpha_eq (hp : Nat.Prime p) : minpoly ℚ (α p) = minpoly ℚ (β p) := by
  grind

/-!
## Definitions to prove Lemma 3
-/
/-- Define the field extension ℚ(α)/ℚ.
In general, if S is a subset of ℝ, the field ℚ(S)
is the smallest intermediate field between ℚ and ℝ containing S. -/
noncomputable def Q_a : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({α p} : Set ℝ)

/-- Define the field extension ℚ(β)/ℚ -/
noncomputable def Q_b : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({β p} : Set ℝ)

/-- α is integral -/
lemma hα_int : IsIntegral ℚ (α p) := ⟨m_alpha p, m_alpha_monic p, eval_alpha_zero p⟩

/-- β is integral -/
lemma hβ_int (p : ℕ) (hp : Nat.Prime p) : IsIntegral ℚ (β p) :=
  ⟨m_alpha p, m_alpha_monic p, eval_beta_zero p hp⟩

/-- Build Kronecker's construction using a root of the
irreducible polynomial m_alpha: ℚ(α) ≅ Q[x]/(m_alpha(x)) -/
noncomputable def isom_min_a_Qa (p : ℕ) : AdjoinRoot (minpoly ℚ (α p)) ≃ₐ[ℚ] ℚ⟮α p⟯ := by
  exact (IntermediateField.adjoinRootEquivAdjoin (F := ℚ) (E := ℝ) (α := α p) (hα_int p))

/-- Build Kronecker's construction using a root of the
irreducible polynomial m_alpha: ℚ(β) ≅ Q[x]/(m_alpha(x)) -/
noncomputable def isom_min_b_Qb (p : ℕ) (hp : Nat.Prime p) :
    AdjoinRoot (minpoly ℚ (β p)) ≃ₐ[ℚ] ℚ⟮β p⟯ := by
  exact (IntermediateField.adjoinRootEquivAdjoin (F := ℚ) (E := ℝ) (α := β p) (hβ_int p hp))

/-!
## Lemmas to prove Lemma 3
-/
/-- The field extensions ℚ(α) and ℚ(β) are isomorphic. -/
noncomputable def isom_Qa_Qb (p : ℕ) (hp : Nat.Prime p) : Q_a p  ≃ₐ[ℚ] Q_b p := by
-- Use algEquiv.trans and AlgEquiv.symm for transitivity and symmetry of isomorphisms.
  have hmin : minpoly ℚ (α p) = minpoly ℚ (β p) := min_pol_beta_alpha_eq p hp
  have hAd : AdjoinRoot (minpoly ℚ (α p)) ≃ₐ[ℚ] AdjoinRoot (minpoly ℚ (β p)) := by
    rw [hmin]
  exact (isom_min_a_Qa p).symm.trans (hAd.trans (isom_min_b_Qb p hp))

/-!
## Lemmas to prove Lemma 4
-/
/-- β ≠ 0 -/
lemma beta_no_zero (p : ℕ) (hp : Nat.Prime p) : β p ≠ 0 := by
  -- More generally proof that β < 0
  have hβ0 : 0 < β p := by
    rw [β]
    have hineq := ineq_sqrtp p hp
    -- Prove √p < p
    have hsub : Real.sqrt (p : ℝ) < (p : ℝ) := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hne : √(p : ℝ) ≠ p := by
        simp only [ne_eq, Nat.cast_nonneg, Real.sqrt_eq_iff_eq_sq]
        intro h
        have : (p : ℝ) * ((p : ℝ) - 1) = 0 := by
          ring_nf; linarith
        have := mul_eq_zero.mp this
        cases this with
        | inl h0 => linarith
        | inr h1 => linarith

      exact lt_of_le_of_ne hineq hne
    -- Prove √p < p
    have harg : 0 < (p : ℝ) - Real.sqrt (p : ℝ) := by linarith
    exact Real.sqrt_pos.mpr harg
  exact ne_of_gt hβ0

/-- α ≠ 0 -/
lemma alpha_no_zero (p : ℕ) (hp : Nat.Prime p) : α p ≠ 0 := by
  -- More generally proof that α < 0
  have hα0 : 0 < α p := by
    rw [α]
    have hineq := ineq_sqrtp p hp
    -- Prove 0 < p + √p
    have harg : 0 < (p : ℝ) + Real.sqrt (p : ℝ) := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hsqrtp : Real.sqrt (p : ℝ) ≥ 0 := by positivity
      have hp0 : 0 < (p : ℝ) := by linarith
      exact add_pos_of_pos_of_nonneg hp0 hsqrtp
    exact Real.sqrt_pos.mpr harg
  exact ne_of_gt hα0

/-- We can rewrite α in terms of β -/
lemma alpha_intermsof_beta (hp : Nat.Prime p) :
    α p = -(β p)⁻¹ * ((β p)^2 - p) * Real.sqrt (p - 1) := by
  have h1 : ((β p)^2 - p) = (-1) * Real.sqrt p := by
    rw [β, Real.sq_sqrt]
    · linarith
    · linarith [ineq_sqrtp p hp]
  have h2 : Real.sqrt p * Real.sqrt (p - 1) = (α p) * (β p) := by
    rw [α, β]
    have hp0 : 0 ≤ (p : ℝ) := by positivity
    have hp1 : 0 ≤ (p : ℝ) - 1 := by
      have h1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt;
      linarith
    have hpos1 : 0 ≤ (p : ℝ) + Real.sqrt p := by positivity
    have hpos2 : 0 ≤ (p : ℝ) - Real.sqrt p := by linarith [ineq_sqrtp p hp]

    have hL := Real.sqrt_mul hp0
    have hR := Real.sqrt_mul hpos1
    rw [← hR (p - Real.sqrt (p : ℝ)), ← hL (p - 1)]
    ring_nf; simp only [Nat.cast_nonneg, Real.sq_sqrt]; ring_nf

  rw [h1]; simp only [neg_mul, one_mul, mul_neg, neg_neg, mul_assoc]; rw [h2]
  simp only [mul_comm, mul_assoc]
  have hβ : β p ≠ 0 := beta_no_zero p hp
  simp only [ne_eq, hβ, not_false_eq_true, mul_inv_cancel₀, mul_one]

/-- We can rewrite β in terms of α -/
lemma beta_intermsof_alpha (hp : Nat.Prime p) : β p = (α p)⁻¹ * ((α p)^2 - p) * Real.sqrt (p - 1) := by
  -- The proof is symmetric to the previous one, and we omit it here for shortness of the code.
  sorry

/-- Suppose that √(p-1) is a rational number. Then, α belongs to ℚ(β) -/
lemma hα_in_Qb (r : ℚ) (hr : ↑r = √(↑p - 1)) (hp : Nat.Prime p) : α p ∈ Q_b p := by
  -- To show α ∈ Q_b, use alpha_intermsof_beta lemma
  rw [alpha_intermsof_beta p hp, ← hr]
  refine IntermediateField.mul_mem (Q_b p) ?_ ?_ -- Suggested by `apply?`
  · have hbeta : β p ∈ Q_b p := by
      simp only [Q_b]; exact mem_adjoin_simple_self ℚ (β p) -- Suggested by `exact?`
    have hβ_ne : β p ≠ 0 := beta_no_zero p hp
    refine IntermediateField.mul_mem (Q_b p) ?_ ?_
    · refine IntermediateField.neg_mem (Q_b p) ?_ -- Suggested by `apply?`
      exact IntermediateField.inv_mem (Q_b p) hbeta -- Suggested by `apply?`
    · refine IntermediateField.sub_mem (Q_b p) ?_ ?_ -- Suggested by `apply?`
      · exact pow_mem hbeta 2
      · exact IntermediateField.natCast_mem (Q_b p) p -- Suggested by `apply?`
  · simp only [SubfieldClass.ratCast_mem] -- Suggested by `apply?`

/-- Suppose that √(p-1) is a rational number. Then, β belongs to ℚ(α) -/
lemma hβ_in_Qa (r : ℚ) (hr : ↑r = √(↑p - 1)) (hp : Nat.Prime p) : β p ∈ Q_a p := by
  -- To show β ∈ Q_a, use beta_intermsof_alpha lemma
  rw [beta_intermsof_alpha p hp, ← hr]
  refine IntermediateField.mul_mem (Q_a p) ?_ ?_
  · have halpha : α p ∈ Q_a p := by
      simp only [Q_a]; exact mem_adjoin_simple_self ℚ (α p)
    have hα_ne : α p ≠ 0 := alpha_no_zero p hp
    refine IntermediateField.mul_mem (Q_a p) ?_ ?_
    · exact IntermediateField.inv_mem (Q_a p) halpha
    · refine IntermediateField.sub_mem (Q_a p) ?_ ?_
      · exact pow_mem halpha 2
      · exact IntermediateField.natCast_mem (Q_a p) p
  · simp only [SubfieldClass.ratCast_mem]

/-- The field extensions ℚ(α) and ℚ(β) are the same subfield of ℂ (if √p-1 ∈ ℚ) -/
lemma Qa_eq_Qb (hp : Nat.Prime p) (h : ∃ r : ℚ, (r : ℝ) = Real.sqrt (p - 1)) : Q_a p = Q_b p := by
  rcases h with ⟨r, hr⟩
  have hα : α p ∈ Q_b p := hα_in_Qb p r hr hp
  have hβ : β p ∈ Q_a p := hβ_in_Qa p r hr hp

  -- ℚ(α) ⊆ ℚ(β)
  have h₁ : Q_a p ≤ Q_b p := by
    rw [Q_a, Q_b]
    simpa only [adjoin_le_iff, singleton_subset_iff] using hα

  -- ℚ(β) ⊆ ℚ(α) (same argument swapping α and β)
  have h₂ : Q_b p ≤ Q_a p := by
    rw [Q_b, Q_a]
    simpa only [adjoin_le_iff, singleton_subset_iff] using hβ

  exact le_antisymm h₁ h₂

/-!
## Definitions to prove Lemma 5
-/
/-- Define the field extension ℚ(α,β) -/
noncomputable def Q_ab : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({α p, β p} : Set ℝ)

/-!
## Lemmas to prove Lemma 5
-/

lemma alpha_ne_beta (p : ℕ) (hp : Nat.Prime p) : (α p) > (β p) := by
  rw [α, β]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine (Real.sqrt_lt_sqrt_iff_of_pos ?_).mpr ?_
  · positivity
  · have hpos : 0 < Real.sqrt (p : ℝ) := by
      positivity
    linarith

lemma alpha_ge_malpha (p : ℕ) (hp : Nat.Prime p) : (α p) > -(α p) := by
  have hα0 : 0 < α p := by
    rw [α]
    have hineq := ineq_sqrtp p hp
    have harg : 0 < (p : ℝ) + Real.sqrt (p : ℝ) := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hsqrtp : Real.sqrt (p : ℝ) ≥ 0 := by positivity
      have hp0 : 0 < (p : ℝ) := by linarith
      exact add_pos_of_pos_of_nonneg hp0 hsqrtp
    exact Real.sqrt_pos.mpr harg
  linarith

/-- The extension ℚ(α,β) is algebraic -/
lemma Q_ab_algebraic (p : ℕ) (hp : Nat.Prime p) : Algebra.IsAlgebraic ℚ (Q_ab p) := by
  apply IntermediateField.isAlgebraic_adjoin -- Obtained from LeanSearch
  intros x hx
  rw [Set.mem_insert_iff] at hx
  cases' hx with h1 h2
  · simpa [h1] using hα_int p
  · rw [Set.mem_singleton_iff] at h2
    simpa [h2] using hβ_int p hp

/-- ℚ(α,β) is a splitting field of m_alpha -/
lemma Q_ab_is_splitting_field
    (p : ℕ) (hp : Nat.Prime p)
    (hgen : Q_ab p = IntermediateField.adjoin ℚ ({α p, -α p, β p, -β p} : Set ℝ)) :
    IsSplittingField ℚ (Q_ab p) (m_alpha p) := by
  rw [isSplittingField_iff]
  refine ⟨?splits, ?adjoin_rootSet⟩ -- Suggested by `apply?`
  -- Prove that m_alpha splits in ℚ(α,β)
  · let roots : Finset (ℝ) := {α p, -(α p), β p, -(β p)}
    -- All roots are in ℚ(α,β)
    have hroots : ∀ r ∈ roots, r ∈ Q_ab p := by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, neg_mem_iff, forall_eq,
        and_self, and_self_left, roots]
      constructor
      · exact mem_adjoin_pair_left ℚ (α p) (β p)
      · rw [Q_ab]
        exact mem_adjoin_pair_right ℚ (α p) (β p)
    sorry
    -- The proof is sorried because I started writing it, but it got long very quickly.
    -- It is provable by showing that m_alpha = (X - α)(X - β)(X + α)(X + β), and using hroots

  -- Prove that ℚ(α,β) is the field resulting from adjoining the rootset of m_alpha
  · rw [hgen]
    suffices (m_alpha p).rootSet ℝ = {α p, -α p, β p, -β p} by -- Thomas's idea
      rw [this]
    -- The rootset of m_alpha is {±α, ±β}
    have hroot : (m_alpha p).rootSet ℝ = {α p, -α p, β p, -β p} := by
      -- ±α, ±β are roots
      have hroot1 : aeval (α p) (m_alpha p) = 0 := eval_alpha_zero p
      have hroot2 : aeval (-α p) (m_alpha p) = 0 := sorry -- similarly
      have hroot3 : aeval (β p) (m_alpha p) = 0 := eval_beta_zero p hp
      have hroot4 : aeval (-β p) (m_alpha p) = 0 := sorry -- similarly
      -- ±α, ±β are all different roots
      have alpha_ne_beta : (α p) > (β p) := alpha_ne_beta p hp
      have alpha_ge_malpha : (α p) > -(α p) := alpha_ge_malpha p hp
      have beta_ge_mbeta : (β p) > -(β p) := by sorry -- similarly as before for α.
      -- {±α, ±β} ⊆ rootset of m_alpha
      have hdeg : (m_alpha p).natDegree = 4 := m_alpha_degree_4 p
      have hpnozero : m_alpha p ≠ 0 := by aesop
      let roots : Set (ℝ) := {α p, -(α p), β p, -(β p)}
      have incl1 : ∀ r ∈ roots, r ∈ (m_alpha p).rootSet ℝ := by
        intro r hr
        cases' hr with h1 h2
        · simpa [h1] using (mem_rootSet_of_ne hpnozero).mpr hroot1
        · cases' h2 with h3 h4
          · simpa [h3] using (mem_rootSet_of_ne hpnozero).mpr hroot2
          · cases' h4 with h5 h6
            · simpa [h5] using (mem_rootSet_of_ne hpnozero).mpr hroot3
            · rw [h6]
              exact (mem_rootSet_of_ne hpnozero).mpr hroot4
      have incl2 : roots ⊆ (m_alpha p).rootSet ℝ := by
        exact incl1
      -- |S| = 4 ≤ |(m_alpha p).rootSet ℝ| ≤ natDegree (m_alpha p) = 4
      -- middle inequality can be proved with Polynomial.card_le_degree_of_subset_roots
      -- There should be some lemma saying: is S ⊆ (m_alpha p).rootSet ℝ
      -- and both sets have the same cardinality, they are equal.
      sorry
    exact hroot

/-- The extension ℚ(α,β) is normal -/
lemma Q_ab_normal (p : ℕ) (hp : Nat.Prime p)
    (hgen : Q_ab p = IntermediateField.adjoin ℚ ({α p, -α p, β p, -β p} : Set ℝ))
    : Normal ℚ (Q_ab p) := by
  -- Show it is a splitting field
  have hsplit : IsSplittingField ℚ (Q_ab p) (m_alpha p) :=
    Q_ab_is_splitting_field p hp hgen
  exact Normal.of_isSplittingField (m_alpha p)

/-- The extension ℚ(α,β) is Galois -/
lemma Q_ab_Galois (p : ℕ) (hp : Nat.Prime p)
    (hgen : Q_ab p = IntermediateField.adjoin ℚ ({α p, -α p, β p, -β p} : Set ℝ))
    : IsGalois ℚ (Q_ab p) := by
  -- We use that the extension is normal (thus algebraic) and separable (char ℚ = 0)
  have h_norm : Normal ℚ (Q_ab p) := Q_ab_normal p hp hgen
  -- ℚ(α, β) is separable
  have h_sep : Algebra.IsSeparable ℚ (Q_ab p) := by
    exact Algebra.IsSeparable.of_integral ℚ ↥(Q_ab p)
  exact {to_isSeparable := h_sep, to_normal := h_norm}

/-!
## Definitions to prove Lemma 6
-/

/-- Define the Galois group of ℚ(α,β)/ℚ -/
noncomputable abbrev Gal_Q_ab (p : ℕ) : Type _ := Q_ab p ≃ₐ[ℚ] Q_ab p
-- This means that the type of Gal_Q_ab is the ℚ-algebra automorphisms of Q_ab p

/-!
## Lemmas to prove Lemma 6
-/
/-- Prove that Q_ab p = Q_a p (from previous lemma) -/
lemma hQab_eq (r : ℚ) (hr : ↑r = √(↑p - 1)) (hp : Nat.Prime p) : Q_ab p = Q_a p := by
  -- Idea: Q(α, β) is generated by {α, β} but β ∈ ℚ(α)
  have hβ : β p ∈ Q_a p := hβ_in_Qa p r hr hp
  have hα : α p ∈ Q_a p := by
    exact adjoin_simple_le_iff.mp fun ⦃x⦄ a => a -- Anonymous (lambda) function.
    -- This supplies `adjoin_simple_le_iff.mp` of a prove that
    -- ∀ × ∈ ℝ, x ∈ ℚ(α) → x ∈ ℚ(α), so it proves ℚ(α) ⊆ ℚ(α)

  -- ℚ(α,β) ⊆ ℚ(α)
  have h₁ : Q_ab p ≤ Q_a p := by
    rw [Q_ab, Q_a]
    simp only [adjoin_le_iff]
    intro x hx
    rcases hx with hx | hx
    · subst hx
      simpa only [SetLike.mem_coe]
    · subst hx
      simpa only [SetLike.mem_coe] using hβ
   -- ℚ(α) ⊆ ℚ(α,β)
  have h₂ : Q_ab p ≥ Q_a p := by
    rw [Q_ab, Q_a]
    simp only [ge_iff_le, adjoin_le_iff, singleton_subset_iff, SetLike.mem_coe]
    exact mem_adjoin_pair_left ℚ (α p) (β p)

  exact le_antisymm h₁ h₂

/-- Rewriting ℚ(α) for future lemmas -/
lemma hQ : (Q_a p) = ℚ⟮α p⟯ := rfl

/-- Rewriting ℚ(α, β) for future lemmas -/
lemma hQab (r : ℚ) (hr : ↑r = √(↑p - 1)) (hp : Nat.Prime p) : (Q_ab p) = ℚ⟮α p⟯ :=
  by rw [hQab_eq p r hr hp, hQ]

/-- The degree of the extension ℚ(α,β)/ℚ is 4 -/
lemma deg_ext_Q_ab_4 (p : ℕ) (r : ℚ) (hr : ↑r = √(↑p - 1)) (hp : Nat.Prime p) :
    Module.finrank ℚ (Q_ab p) = 4 := by
  rw [hQab p r hr hp]
  -- Use the degree of the minimal polynomial
  have hα_int : IsIntegral ℚ (α p) :=
    ⟨m_alpha p, m_alpha_monic p, eval_alpha_zero p⟩
  rw [(IntermediateField.adjoin.finrank hα_int), min_pol_alph] -- Found with LeanSearch
  · exact m_alpha_degree_4 p
  · exact hp

/-- There are 4 elements in Gal(ℚ(α,β)/ℚ) -/
lemma card_Gal_Q_ab (p : ℕ) (r : ℚ) (hr : ↑r = √(↑p - 1)) (hp : Nat.Prime p)
    (hgen : Q_ab p = IntermediateField.adjoin ℚ ({α p, -α p, β p, -β p} : Set ℝ)):
    Nat.card (Gal_Q_ab p) = 4 := by
  have hGal : IsGalois ℚ (Q_ab p) := Q_ab_Galois p hp hgen
  have hcard : Nat.card (Gal_Q_ab p) = Module.finrank ℚ (Q_ab p) := by
    simpa [Gal_Q_ab]
    using (IsGaloisGroup.card_eq_finrank -- Found with LeanSearch
      (G := Gal_Q_ab p) (K := ℚ) (L := Q_ab p))
  simpa only [hcard] using deg_ext_Q_ab_4 p r hr hp

/-- We prove that there exists some element of Gal(ℚ(α,β)/ℚ) that has order 4 -/
lemma exists_order4_morphism
    (p : ℕ) (hp : Nat.Prime p)
    (hcard : Nat.card (Gal_Q_ab p) = 4) :
    ∃ σ : Gal_Q_ab p, orderOf σ = 4 := by sorry

-- The proof is sorried because of time constraints.
-- To prove it, take the the non-trivial morphism σ(α) = β,
-- and check that σ^k ≠ id for any 1 ≤ k ≤ 3.

/-- The Galois group of the extension ℚ(α,β)/ℚ is isomorphic to
the cyclic group of order 4, so it is ℤ/4ℤ -/
noncomputable def gal_iso_Zmod4
    (p : ℕ) (hp : Nat.Prime p)
    (hcard : Nat.card (Gal_Q_ab p) = 4) :
    Gal_Q_ab p ≃* Multiplicative (ZMod 4) := by
  have hex : ∃ σ : Gal_Q_ab p, orderOf σ = 4 :=
    exists_order4_morphism p hp hcard
  let σ := Classical.choose hex
  -- Take σ of order 4
  have hσ : orderOf σ = 4 := Classical.choose_spec hex
  have h2 : ∃ σ : Gal_Q_ab p, Nat.card (Gal_Q_ab p) ≤ orderOf σ := by
    refine ⟨σ, by rw [hcard, hσ]⟩
  have hcard2 : 0 < Nat.card (Gal_Q_ab p) := by exact Nat.lt_of_sub_eq_succ hcard
  haveI : Finite (Gal_Q_ab p) := (Nat.card_pos_iff.1 hcard2).2
  -- Prove Gal(ℚ(α,β)/ℚ) is cyclic
  have hcyc : IsCyclic (Gal_Q_ab p) :=
    (isCyclic_iff_exists_natCard_le_orderOf).2 h2
  rw [← hcard]
  simpa using (zmodCyclicMulEquiv (G := Gal_Q_ab p) hcyc).symm

/-!
## Hint to prove Lemma 7
-/
-- Finally, we could use the Galois correspondence to show that the only non-trivial field between ℚ
-- and ℚ(α,β) is ℚ(√p)

--- Run lint at the end to check for (formatting) errors.
#lint
