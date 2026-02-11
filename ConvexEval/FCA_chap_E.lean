import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Standard convention where 0*(+∞) = 0
   The definition of ConvexOn involves uses SMul for both sides of the defining inequality.
 -/
noncomputable instance : SMul ℝ (WithTop ℝ) where
  smul t x := match x with
    | ⊤ => if t = 0 then 0 else ⊤
    | some r => some (t * r)

/-
  Note that we avoid +∞ + (-∞) cases in InProperConvRn with the condition
  that the function cannot be -∞ anywhere.
-/
noncomputable local instance : SMul ℝ (WithBot (WithTop ℝ)) where
  smul t x :=
    match x with
    | ⊥ =>
        if t = 0 then (0 : WithBot (WithTop ℝ)) else ⊥
    | some y =>
        match y with
        | ⊤ =>
            if t = 0 then (0 : WithBot (WithTop ℝ)) else some ⊤
        | some r =>
            some (some (t * r))

/- View a `WithTop ℝ`-valued function as a `WithBot (WithTop ℝ)`-valued one. -/
def liftWTtoEReal {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
  EuclideanSpace ℝ (Fin n) → WithBot (WithTop ℝ)
  := fun x => (f x : WithBot (WithTop ℝ))

/- Helper for getting the first n-coordinates -/
def vecHead {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n)
  := fun i => x (Fin.castSucc i)

/- Helper for getting the last coordinate -/
def vecLast {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ
  := x (Fin.last n)

/- Epigraph of a function -/
def epigraph {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Set (EuclideanSpace ℝ (Fin n) × ℝ)
  := {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ p.2}

/- Effective domain -/
def effDom {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Set (EuclideanSpace ℝ (Fin n))
  := {x : EuclideanSpace ℝ (Fin n) | f x < ⊤}

/- Set of extended real-valued convex functions on ℝ^n -/
def InConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x < ⊤) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y))

/- Closure (lower semi-continuous hull) of a function -/
noncomputable def lscHull {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := Filter.liminf f (𝓝 x)

/- Set of extended real-valued closed convex functions on ℝ^n -/
def InClosedConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x < ⊤) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y)) ∧
     (∀ x, (lscHull f) x = f x)

/- Nondegeneracy conditions for functions -/
def IsNondegenerate {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x ≠ ⊤) ∧ (∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

/- Value finite -/
def IsFinite (z : WithBot (WithTop ℝ)) : Prop :=
  ∃ r : ℝ, z = (r : WithBot (WithTop ℝ))

/- Conjugate of a function (Legendre-Fenchel transform) -/
noncomputable def Conjugate {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (s : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := sSup {z : WithTop ℝ | ∃ x ∈ effDom f, z = inner ℝ s x - f x}

/- Biconjugate of a function -/
noncomputable def Biconjugate {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := sSup {z : WithTop ℝ | ∃ s, z = inner ℝ s x - (Conjugate f s)}

/- Subdifferential -/
def SubdifferentialAt {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n))
  := {s | ∀ y, f y ≥ f x + inner ℝ s (y - x)}

/- Support function of a set -/
noncomputable def SupportFun {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := sSup {z : WithTop ℝ | ∃ s ∈ S, (z = inner ℝ s x)}

/- Asymptotic (recession) function -/
noncomputable def AsymptoticFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x₀ d : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := limUnder Filter.atTop (fun (t : ℝ) => t⁻¹ • (f (x₀ + t • d) - f x₀))

/- Minorizing function (f ≤ g) -/
def Minorizes {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  : Prop
  := ∀ x, f x ≤ g x

/- Indicator function -/
noncomputable def Indicator {n : ℕ}
  (H : Subspace ℝ (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  : WithTop ℝ := by
    classical
    exact if x ∈ H then 0 else ⊤

/- 0-coercive function -/
noncomputable def IsZeroCoerciveFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := Filter.Tendsto f (Filter.comap norm Filter.atTop) Filter.atTop

/- 1-coercive function -/
noncomputable def IsOneCoerciveFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := Filter.Tendsto (fun x => (norm x)⁻¹ • f x) (Filter.comap norm Filter.atTop) Filter.atTop

/- Image of a linear operator -/
def Im {m n : ℕ}
  (A : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
  := {z | ∃ y, A y = z}

/- Infimal convolution -/
noncomputable def infimalConv {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : WithBot (WithTop ℝ)
  := sInf { z : WithBot (WithTop ℝ) | ∃ y : EuclideanSpace ℝ (Fin n),
                                      z = ((f₁ y + f₂ (x - y) : WithTop ℝ) : WithBot (WithTop ℝ)) }

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.1.2 -/
lemma FCA_HUL_1_1_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) :
  InClosedConvRn (Conjugate f) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Example 1.2.1.i -/
lemma FCA_HUL_1_2_1_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) :
  Conjugate f = fun s => sSup {z : WithTop ℝ | ∃ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), (z = inner ℝ s x - r) ∧ ((x, r) ∈ epigraph f)} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Example 1.2.1.ii -/
lemma FCA_HUL_1_2_1_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) :
  let f_conj := fun s => Conjugate f s
  let f_epi_supportfun := fun (s : EuclideanSpace ℝ (Fin n)) (u : ℝ) => SupportFun {z | (vecHead z, vecLast z) ∈ (epigraph f)} (Fin.snoc s (-u))
  let f_dom_supportfun := fun s => SupportFun {z | z ∈ effDom f} s
  f_epi_supportfun = (fun s u =>
    if u > 0 then u • f_conj (u⁻¹ • s)
    else if u = 0 then f_dom_supportfun s
    else ⊤
  ) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.2.2 -/
lemma FCA_HUL_1_2_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f) (hf_closed_convex : InClosedConvRn f)
  (hx₀ : f x₀ ≠ ⊤) :
  let f_conj := fun s => Conjugate f s
  let f_epi_supportfun := fun (s : EuclideanSpace ℝ (Fin n)) (u : ℝ) =>
                               SupportFun {z | (vecHead z, vecLast z) ∈ (epigraph f)} (Fin.snoc s (-u))
  let f_dom_supportfun := fun s => SupportFun {z | z ∈ effDom f} s
  let f_conj_asympfun := fun s => AsymptoticFun f_conj x₀ s
  ∀ s, (f_epi_supportfun s 0 = f_dom_supportfun s) ∧ (f_dom_supportfun s = f_conj_asympfun s) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.i -/
lemma FCA_HUL_1_3_1_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (r : ℝ) (hf_nondegenerate : IsNondegenerate f) :
  let g := fun x => f x + r
  let f_conj := fun s => Conjugate f s
  let g_conj := fun s => Conjugate g s
    ∀ s, g_conj s = f_conj s - r := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.ii -/
lemma FCA_HUL_1_3_1_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (t : ℝ)
  (hf_nondegenerate : IsNondegenerate f) (ht_pos : t > 0)
  : let g := fun x => t • f x
    let f_conj := fun s => Conjugate f s
    let g_conj := fun s => Conjugate g s
    ∀ s, g_conj s = t • f_conj (t⁻¹ • s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.iii -/
lemma FCA_HUL_1_3_1_iii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (t : ℝ)
  (hf_nondegenerate : IsNondegenerate f) (ht_nonzero : t ≠ 0)
  : let g := fun x => f (t • x)
    let f_conj := fun s => Conjugate f s
    let g_conj := fun s => Conjugate g s
    ∀ s, g_conj s = f_conj (t⁻¹ • s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.iv -/
lemma FCA_HUL_1_3_1_iv {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (A : (EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n)))
  (hf_nondegenerate : IsNondegenerate f)
  : let g := fun x => f (A x)
    let A_adjoint_inverse : (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
                            (A.symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).adjoint
    ∀ s, Conjugate g s = Conjugate f (A_adjoint_inverse s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.v -/
lemma FCA_HUL_1_3_1_v {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : let g := fun x => f (x - x₀)
    ∀ s, Conjugate g s = Conjugate f s + inner ℝ s x₀
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.vi -/
lemma FCA_HUL_1_3_1_vi {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (s₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : let g := fun x => f x + inner ℝ s₀ x
    ∀ s, Conjugate g s = Conjugate f (s - s₀)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.vii -/
lemma FCA_HUL_1_3_1_vii {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f₁ ∧ IsNondegenerate f₂)
  (hf₁_minorizes : Minorizes f₁ f₂)
  : Minorizes (Conjugate f₂) (Conjugate f₁)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.viii -/
lemma FCA_HUL_1_3_1_viii {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (α : ℝ)
  (hf_nondegenerate : IsNondegenerate f₁ ∧ IsNondegenerate f₂)
  : Set.Nonempty (effDom f₁ ∩ effDom f₂) → α ∈ Set.Ioo 0 1 →
    Minorizes (Conjugate (fun x => α • f₁ x + (1 - α) • f₂ x))
              (α • (Conjugate f₁) + (1 - α) • (Conjugate f₂))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.2 -/
lemma FCA_HUL_1_3_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (H : Subspace ℝ (EuclideanSpace ℝ (Fin n)))
  (hf_nondegenerate : IsNondegenerate f)
  : let pH : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => Submodule.orthogonalProjection H x
    let g := fun x => f x + (Indicator H) x
    ∀ s, Conjugate g s = Conjugate (f ∘ pH) (pH s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.4 -/
lemma FCA_HUL_1_3_4 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (V : Subspace ℝ (EuclideanSpace ℝ (Fin n)))
  (hf_nondegenerate : IsNondegenerate f) (hV_contains_affdom : affineSpan ℝ (effDom f))
  : let U := Vᗮ
    let pV : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => Submodule.orthogonalProjection V x
    let pU : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => Submodule.orthogonalProjection U x
    ∀ z ∈ affineSpan ℝ (effDom f), ∀ s,
    Conjugate f s = inner ℝ (pU s) z + Conjugate f (pV s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.3.5 -/
lemma FCA_HUL_1_3_5 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (hf_nondegenerate : IsNondegenerate f)
  : epigraph (Biconjugate f) = closure (convexHull ℝ (epigraph f))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.3.6.i -/
lemma FCA_HUL_1_3_6_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hg : (Minorizes (Biconjugate f) g) ∧ (Minorizes g f))
  : ∀ s, Conjugate g s = Conjugate f s
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.3.6.ii -/
lemma FCA_HUL_1_3_6_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  : (Biconjugate f = f) ↔ (InClosedConvRn f)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.8 -/
lemma FCA_HUL_1_3_8 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) (hf_coercive : IsOneCoerciveFun f)
  : ∀ s, Conjugate f s < ⊤
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.9.i -/
lemma FCA_HUL_1_3_9_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : x₀ ∈ interior (effDom f) → IsZeroCoerciveFun (fun x => Conjugate f x - inner ℝ x₀ x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.9.ii -/
lemma FCA_HUL_1_3_9_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f)
  : ∀ x, f x ≠ ⊤ → IsOneCoerciveFun (Conjugate f)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Remark 1.3.10.i -/
lemma FCA_HUL_1_3_10_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f) (hf_closed_convex : InClosedConvRn f)
  : x₀ ∈ interior (effDom f) ↔ IsZeroCoerciveFun (fun x => Conjugate f x - inner ℝ x₀ x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Remark 1.3.10.ii -/
lemma FCA_HUL_1_3_10_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) (hf_closed_convex : InClosedConvRn f)
  : ∀ (x : EuclideanSpace ℝ (Fin n)), x ∈ (effDom f) ↔ IsOneCoerciveFun (Conjugate f)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.1 -/
lemma FCA_HUL_1_4_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x s : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : s ∈ SubdifferentialAt f x ↔ (Conjugate f s) + f x - (inner ℝ s x) = 0
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.2 -/
lemma FCA_HUL_1_4_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : InConvRn f)
  : x ∈ intrinsicInterior ℝ (effDom f) → Set.Nonempty (SubdifferentialAt f x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.3.i -/
lemma FCA_HUL_1_4_3_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : Set.Nonempty (SubdifferentialAt f x) → Biconjugate f x = f x
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.3.ii -/
lemma FCA_HUL_1_4_3_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : (Minorizes (Biconjugate f) g) ∧ (Minorizes g f) ∧ (g x = f x) → (SubdifferentialAt g x) = (SubdifferentialAt f x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.3.iii -/
lemma FCA_HUL_1_4_3_iii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x s : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : s ∈ SubdifferentialAt f x → x ∈ SubdifferentialAt (Conjugate f) s
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Corollary 1.4.4 -/
lemma FCA_HUL_1_4_4 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x s : EuclideanSpace ℝ (Fin n))
  (hf_closed_convex : InClosedConvRn f)
  : List.TFAE [
    f x + Conjugate f s - inner ℝ s x = 0,
    s ∈ SubdifferentialAt f x,
    x ∈ SubdifferentialAt (Conjugate f) s
  ]
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Corollary 2.1.1 -/
lemma FCA_HUL_2_1_1 {m n : ℕ}
  (g : EuclideanSpace ℝ (Fin m) → WithTop ℝ)
  (A : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)))
  (hg_nondegenerate : IsNondegenerate g)
  (h_nonempty_domain : Set.Nonempty ((Im A.adjoint) ∩ effDom (Conjugate g)))
  : let h := fun x => sInf (Set.image g {y | A y = x})
    ∀ s, Conjugate h s = Conjugate g (A.adjoint s)
  := by sorry

-- /- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Corollary 2.1.3 -/
-- lemma FCA_HUL_2_1_3 {n : ℕ}
--   (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
--   (hf_not_infinity : ∃ x₁, f₁ x₁ ≠ ⊤ ∧ ∃ x₂, f₂ x₂ ≠ ⊤)
--   (h_nonempty_domain : Set.Nonempty (effDom (Conjugate (liftWTtoEReal f₁)) ∩ effDom (Conjugate (liftWTtoEReal f₂))))
--   : let inf_conv := infimalConv f₁ f₂
--   (IsNondegenerate inf_conv) ∧
--   (∀ s, Conjugate inf_conv s = (Conjugate (liftWTtoEReal f₁) s) + (Conjugate (liftWTtoEReal f₂) s))
--   := by sorry
