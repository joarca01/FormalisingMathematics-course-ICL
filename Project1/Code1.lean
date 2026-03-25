import Mathlib

--- Silence docstring, spaces and Simpa warnings
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unnecessarySimpa false

open Set

/-!
# Limits on open intervals

This file defines an ε–δ limit predicate `limit_f_x_0` for functions on the subtype
`Set.Ioo a b` (open interval (a,b)) and basic derived notions of continuity
and boundedness near a point x₀.

Main definitions:
- `limit_f_x_0`: limit of a function f at some point x₀ ∈ (a,b).
- `continuous_x0`: continuity of f at a point `x₀ ∈ Set.Ioo a b`.
- `bounded_on_I`: boundedness of a function on a (relative) set I.

Main result:
We prove that if `f` has a limit at `x₀`, then `f` is bounded
on some neighborhood (interval) of `x₀`.

## References
⋆ [Francesc Mañosas, ⋆Notes on Real-valued functions ⋆, Autonomous University of Barcelona, 2019]
-/

/- Definitions -/

--- Define interval endpoints
variable (a b : ℝ)

/-- Classical definiton of limit of a function f at the point `x₀`,
where `f : Ioo a b → ℝ` is defined in the open interval (a,b), with limit value `l`. -/
def limit_f_x_0 {a b : ℝ} (l x₀ : ℝ) (f : Set.Ioo a b → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : Set.Ioo a b, |x - x₀| < δ ∧ |x - x₀| > 0 → |f x - l| < ε

/-- Classical definiton of the continuity of `f : Ioo a b → ℝ` in a point `x₀`:
the limit `l` at `x₀` is equal to `f x₀`. -/
def continuous_x0 {a b : ℝ} (f : Set.Ioo a b → ℝ) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b) : Prop :=
  limit_f_x_0 (l := f ⟨x₀, hx₀⟩) x₀ f

-- Observe that `f ⟨x₀, hx₀⟩` means:
-- "Evaluate f at the point `x₀`, regarded as an element of the
-- restricted domain (a, b) using the proof `hx₀`."

/-- Classical definiton of the continuity of `f : Ioo a b → ℝ` everywhere in the interval. -/
def continuous_on_interval (f : Set.Ioo a b → ℝ) : Prop :=
  ∀ x₀ (hx₀ : x₀ ∈ Set.Ioo a b), continuous_x0 f x₀ hx₀

/-- Classical definiton of the continuity of `f : ℝ → ℝ` everywhere in ℝ -/
def continuous_on_R (f : ℝ → ℝ) : Prop :=
  ∀ a b x₀ (hx₀ : x₀ ∈ Set.Ioo a b),
    continuous_x0 (fun x : Set.Ioo a b => f x) x₀ hx₀

/--- Example ---/

--- We will use the above definitions to prove a basic limit.
/- The function g(x) = x has limit x₀ = g(x₀) in every point x₀ ∈ ℝ.
I.e., the function g(x) is continuous on ℝ. -/

def linear_fun : ℝ → ℝ := fun x => x

example : continuous_on_R linear_fun := by
  -- introduce assumptions that `continuous_on_R` expects.
  intro a b x₀ hx₀
  -- unfold continuity (and limit) at x₀
  dsimp [continuous_x0, limit_f_x_0]
  intro ε hε
  -- choose δ = ε and provide proof that δ > 0
  refine ⟨ε, hε, ?_⟩
  -- hx is the hypothesis: |x - x₀| < ε and |x - x₀| > 0
  intro x hx
  -- `[linear_fun]` replaces `f` by its specific definition
  simpa [linear_fun] using hx.1

/- More definitions -/

--- We will now introduce the notion of boundedness at `x₀`.

/-- Def 1: Boundness of f in the interval (a,b) -/
def bounded_on_interval_1 (f : Set.Ioo a b → ℝ) : Prop :=
  ∃ (M m : ℝ), ∀ x : Set.Ioo a b, m ≤ f x ∧ f x ≤ M

/-- Def 2: Boundness of f in the interval (a,b) -/
def bounded_on_interval_2 (f : Set.Ioo a b → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Set.Ioo a b, |f x| ≤ K

/-- Equivalence of the two boundedness definitions. -/
lemma bounded_equiv (f : Set.Ioo a b → ℝ) :
  bounded_on_interval_1 a b f ↔
  bounded_on_interval_2 a b f := by
  -- separate the two implications
  constructor
  · -- (Def 1) → (Def 2)
    intro h
    -- unpack hypothesis and substitute
    rcases h with ⟨M, m, hMm⟩
    -- define bound for Def 2 with m, M
    let K0 : ℝ := max (|m|) (|M|)
    -- unpack what needs to be proved with K0
    refine ⟨K0, ?_, ?_⟩
    · -- prove K0 ≥ 0
      have hm : 0 ≤ |m| := abs_nonneg m
      have hmk : |m| ≤ K0 := le_max_left _ _ -- the underscores tell Lean to infer the arguments
      exact hm.trans hmk
    · -- prove |f x| ≤ K0
      intro x
      -- prove -K0 ≤ f x
      have hx_low : -K0 ≤ f x := by
        -- use -K0 ≤ -|m| ≤ m ≤ f x
        have h1 : -K0 ≤ -|m| := by
          have : |m| ≤ K0 := le_max_left _ _
          exact neg_le_neg this -- `this` refers to the last `have` statement
        have h2 : -|m| ≤ m := by linarith [neg_le_abs m]
        have h3 : m ≤ f x := by simpa using (hMm x).1
        exact h1.trans (h2.trans h3)
      -- prove fx ≤ K0
      have hx_up : f x ≤ K0 := by
        -- f x ≤ M ≤ |M| ≤ K0
        have hfxM : f x ≤ M := (hMm x).2
        have hMabs : M ≤ |M| := le_abs_self M
        have habsK : |M| ≤ K0 := le_max_right _ _
        exact hfxM.trans (hMabs.trans habsK)
      exact (abs_le.mpr ⟨hx_low, hx_up⟩) -- mpr uses the reverse implication of `abs_le`.
      -- the ⟨,⟩ brackets are used to construct a hypotheses of type A ∧ B

  · -- (Def 2) → (Def 1)
      intro h
      rcases h with ⟨K, Kpos, hK⟩
      -- take m = -K, M = K. Then, |f x| ≤ K → -K ≤ f x ≤ K
      refine ⟨K, -K, ?_⟩
      intro x
      -- abs_le.mp: |f x| ≤ K means -K ≤ f x ∧ f x ≤ K
      simpa using (abs_le.mp (hK x)) -- mp uses the direct implication of `abs_le`

-- Define a local notion of boundness --
/-- Boundedness of f on a set J ⊆ (a,b) ⊆ ℝ -/
def bounded_on_J {a b : ℝ} (J : Set ℝ) (f : Set.Ioo a b → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ J, ∀ hx : x ∈ Set.Ioo a b, |f ⟨x, hx⟩| ≤ K

/--- Main Result ---/

/- If a function `f` has a limit at `x₀`, then `f` is bounded
in the open interval (x₀ - δ, x₀ + δ) for some `δ > 0`. -/
lemma bounded_if_limit_exists (f : Set.Ioo a b → ℝ) (x₀ l : ℝ) (hx0ab : x₀ ∈ Set.Ioo a b) :
    limit_f_x_0 l x₀ f → ∃ δ > 0, bounded_on_J (Set.Ioo (x₀ - δ) (x₀ + δ)) f := by
  intro hlim
  -- use definition of limit with ε = 1
  obtain ⟨δ, hδpos, hδ⟩ := hlim 1 (by norm_num)
  -- define one possible bound
  let K₁ : ℝ := 1 + |l|
  -- |f x| < K₁ if |x - x₀| < δ and |x - x₀| > 0
  have hδ_to_K1 :
  ∀ x : Set.Ioo a b,
    (|x - x₀| < δ ∧ |x - x₀| > 0) → |f x| < K₁ :=
  by
    intro x hx
    -- use triangle inequality to see |f x| ≤ |f x - l| + |l|
    have triang : |f x| ≤ |f x - l| + |l| := by
      -- norm_add_le does: |a + b|  ≤ |a| + |b|
      have := norm_add_le (f x - l) l
      simpa using this
    -- |f x - l| < 1
    have hfxl : |f x - l| < 1 := hδ x hx
    -- transform to: |f x - l| + |l| < 1 + |l| = K₁
    have add_l : |f x - l| + |l| < K₁ := by
      -- add_lt_add_right does: if a < b then a + c < b + c
      simpa [K₁] using add_lt_add_right hfxl |l|
    -- conclude |f x| < K₁
    exact lt_of_le_of_lt triang add_l

  -- define the final upper bound
  let K₂ : ℝ := max K₁ |f ⟨x₀, hx0ab⟩|
  -- simplify hypothesis and split goals
  refine ⟨δ, hδpos, ?_⟩
  refine ⟨K₂, ?_, ?_⟩
  · -- prove 0 ≤ K₂
    -- prove 1 ≤ K₁ = 1 + |l|, since |l| ≥ 0
    have h1leqK1 : 1 ≤ K₁ := by
      have habs : 0 ≤ |l| := abs_nonneg l
      -- 1 ≤ 1 + |l|
      linarith [habs]
    -- prove K₁ ≤ K₂ = max K₁ |f x₀|
    have hK1leqK2 : K₁ ≤ K₂ := by
      simpa [K₂] using le_max_left K₁ |f ⟨x₀, hx0ab⟩|
    exact (le_trans (by norm_num) (h1leqK1.trans hK1leqK2))
  · -- prove |f x| ≤ K₂ for x ∈ (x₀ - δ, x₀ + δ)
    intro x hxI hxDom
    by_cases hxeq : x = x₀ -- observe x satisfies both hxI and hxDom
    · -- bound the case x = x₀
      have hx0_le_K2 : |f ⟨x₀, hx0ab⟩| ≤ K₂ :=
        le_max_right _ _
      have : |f ⟨x, hxDom⟩| ≤ K₂ := by
        simpa [hxeq] using hx0_le_K2
      exact this
    · -- bound the case x ≠ x₀, i.e., |x - x₀| < δ and 0 < |x - x₀|
      have hx_abs_ld : |x - x₀| < δ := by
        have hL : -δ < x - x₀ := by linarith [hxI.1]
        have hR : x - x₀ < δ := by linarith [hxI.2]
        exact abs_lt.mpr ⟨hL, hR⟩
      have hpos_abs : |x - x₀| > 0 := abs_pos.mpr (sub_ne_zero.mpr hxeq)
      -- bound |f x| < K₁ for x ∈ 0 < |x - x₀| < δ
      have flK1 : |f ⟨x, hxDom⟩| < K₁ :=
        -- use |x - x₀| < δ and 0 < |x - x₀|
        hδ_to_K1 ⟨x, hxDom⟩ ⟨by simpa using hx_abs_ld, hpos_abs⟩
      -- K₁ ≤ K₂
      have K₁_le_K₂ : K₁ ≤ K₂ := by
        simpa [K₂] using (le_max_left _ _)
      -- conclude |f x| ≤ K₂
      exact (le_of_lt flK1).trans K₁_le_K₂

--- Run lint at the end to check for (formatting) errors.
#lint
