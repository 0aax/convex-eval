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

def effDom {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithBot (WithTop ℝ)) : Set (EuclideanSpace ℝ (Fin n))
  := {x : EuclideanSpace ℝ (Fin n) | f x < ⊤ ∧ f x > ⊥}

def epigraph {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Set (EuclideanSpace ℝ (Fin n) × ℝ)
  := {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ p.2}

def strictEpigraph {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Set (EuclideanSpace ℝ (Fin n) × ℝ)
  := {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 < p.2}

def Δκ (k : ℕ) : Set (EuclideanSpace ℝ (Fin k))
    := {v : (EuclideanSpace ℝ (Fin k)) | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

noncomputable def lscHull {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := Filter.liminf f (𝓝 x)

def InConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x < ⊤) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y))

def InClosedConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x < ⊤) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y)) ∧
     (∀ x, (lscHull f) x = f x)

def affineHull {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
  := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → (EuclideanSpace ℝ (Fin n))) (_ : ∀ i, x i ∈ C),
     {v : (EuclideanSpace ℝ (Fin n)) |
      ∃ (a : (EuclideanSpace ℝ (Fin k))), (∑ i, a i = 1) ∧ (v = ∑ i, a i • x i)}

def sublevelSet {n : ℕ}
  (r : ℝ) (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  : Set (EuclideanSpace ℝ (Fin n))
  := {x : EuclideanSpace ℝ (Fin n) | f x ≤ r}

def parallelSubspace {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
  := {v : EuclideanSpace ℝ (Fin n) | ∃ x, ∃ y, (x ∈ S) ∧ (y ∈ S) ∧ (v = x - y)}

noncomputable def lowerBoundFunction {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n) × ℝ)) (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := sInf {r : WithTop ℝ | ∃ (z : EuclideanSpace ℝ (Fin n) × ℝ), (z ∈ C) ∧ (x = z.1) ∧ (r = z.2)}

def minorizedAt {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n) × ℝ)) (x : EuclideanSpace ℝ (Fin n)) : Prop
  := let K := {r : ℝ | ∃ (z : EuclideanSpace ℝ (Fin n) × ℝ), (z ∈ C) ∧ (x = z.1) ∧ (r = z.2)}
     ∃ (k₀ : ℝ), ∀ r ∈ K, r ≥ k₀

noncomputable def perspective {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (u : ℝ) (x : EuclideanSpace ℝ (Fin n))
  : WithTop ℝ :=
  if u > 0 then
    u * f (u⁻¹ • x)
  else
    ⊤

def InProperConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithBot (WithTop ℝ)) : Prop
  := (∃ x, f x < ⊤) ∧ (∀ x, f x ≠ ⊥) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y))

noncomputable def infimalConv {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : WithBot (WithTop ℝ)
  := sInf {z : WithBot (WithTop ℝ) | ∃ y, z = f₁ y + f₂ (x - y)}

noncomputable def imageFun {m n : ℕ}
  (A : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)))
  (g : EuclideanSpace ℝ (Fin m) → WithBot (WithTop ℝ))
  (x : EuclideanSpace ℝ (Fin n)) : WithBot (WithTop ℝ)
  := sInf (Set.image g {y : EuclideanSpace ℝ (Fin m) | A y = x})

noncomputable def valueFun {p n : ℕ}
  (phi : EuclideanSpace ℝ (Fin p) → WithBot (WithTop ℝ))
  (c : (Fin n) → (EuclideanSpace ℝ (Fin p) → WithBot (WithTop ℝ)))
  (x : EuclideanSpace ℝ (Fin n)) : WithBot (WithTop ℝ)
  := sInf (Set.image phi {u | ∀ j, (c j) u ≤ x j})

noncomputable def marginalFun {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin (n + m)) → WithBot (WithTop ℝ))
  (x : EuclideanSpace ℝ (Fin n)) : WithBot (WithTop ℝ)
  := let g_concat : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → WithBot (WithTop ℝ) := fun a b
                     => g (Fin.append (α := ℝ) a b)
     sInf (Set.range (g_concat x))

def Minorizes {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  : Prop
  := ∀ x, f x ≤ g x

/- View a `WithTop ℝ`-valued function as a `WithBot (WithTop ℝ)`-valued one. -/
def liftWithTop {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
  EuclideanSpace ℝ (Fin n) → WithBot (WithTop ℝ)
  := fun x => (f x : WithBot (WithTop ℝ))

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.1.2 -/
lemma FCA_chap_B_1_1_2 {n : ℕ}
  (c : ℝ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hC_nonempty : Set.Nonempty C) (hC_convex : Convex ℝ C)
  : StrongConvexOn C c f ↔ ConvexOn ℝ C (fun x => f x - (c/2) * ‖x‖^2)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.1.6 -/
lemma FCA_chap_B_1_1_6 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (hf_nonemptyDomain : ∃ x, f x < ⊤)
  : List.TFAE [
    ConvexOn ℝ Set.univ f,
    Convex ℝ (epigraph f),
    Convex ℝ (strictEpigraph f)
  ]
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Theorem 1.1.8 (Jensen's Inequality) -/
lemma FCA_chap_B_1_1_8 {n : ℕ}
  (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hC_convex : InConvRn f)
  : ∀ (x : Fin k → EuclideanSpace ℝ (Fin n)), ∀ (α : EuclideanSpace ℝ (Fin k)),
    α ∈ Δκ k → f (∑ i, (α i) • (x i)) ≤ ∑ i, (α i) • f (x i)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.1.9 -/
lemma FCA_chap_B_1_1_9 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_convex : InConvRn f)
  : intrinsicInterior ℝ (epigraph f) =
    {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ intrinsicInterior ℝ (effDom (liftWithTop f)) ∧ p.2 > f p.1}
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.2.1 -/
lemma FCA_chap_B_1_2_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_convex : InConvRn f)
  : ∀ (x₀ : EuclideanSpace ℝ (Fin n)), (x₀ ∈ intrinsicInterior ℝ (effDom (liftWithTop f))) →
    ∃ (s : EuclideanSpace ℝ (Fin n)), ∀ (x : EuclideanSpace ℝ (Fin n)),
    (s ∈ parallelSubspace (affineHull (effDom (liftWithTop f)))) ∧ (f x ≥ f x₀ + inner ℝ s (x - x₀))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.2.2 -/
lemma FCA_chap_B_1_2_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  : LowerSemicontinuousOn f Set.univ ↔ (
      IsClosed (epigraph f) ↔ ∀ (r : ℝ), IsClosed (sublevelSet r f)
    )
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.2.5 -/
lemma FCA_chap_B_1_2_5 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_convex : InConvRn f) (hx : x₀ ∈ intrinsicInterior ℝ (effDom (liftWithTop f)))
  : ∀ x, Filter.Tendsto (fun t => f (x + t • (x₀ - x))) (𝓝 0) (𝓝 (lscHull f x))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.2.6 -/
lemma FCA_chap_B_1_2_6 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (hf_convex : InConvRn f)
  : let cl_f := lscHull f
    (InConvRn cl_f) ∧ (∀ x ∈ intrinsicInterior ℝ (effDom (liftWithTop f)), cl_f x = f x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.2.8 -/
lemma FCA_chap_B_1_2_8 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (hf_convex : InConvRn f)
  : let cl_f := lscHull f
    ∀ x, cl_f x = sSup {v : ℝ | ∃ (z : EuclideanSpace ℝ (Fin n) × ℝ),
                                (v = inner ℝ z.1 x - z.2) ∧ (∀ y, (inner ℝ z.1 y) - z.2 ≤ f y)}
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.3.1.i -/
lemma FCA_chap_B_1_3_1_i {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n) × ℝ))
  (hC_nonempty : Nonempty C) (hC_minorized : ∀ x, minorizedAt C x) (hC_convex : Convex ℝ C)
  : InConvRn (lowerBoundFunction C)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 1.3.1.ii -/
lemma FCA_chap_B_1_3_1_ii {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n) × ℝ))
  (hC_nonempty : Nonempty C) (hC_minorized : ∀ x, minorizedAt C x)
  (hC_convex : Convex ℝ C) (hC_closed : IsClosed C)
  : (InClosedConvRn (lowerBoundFunction C))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.1.1.i -/
lemma FCA_chap_B_2_1_1_i {n : ℕ} {m : ℕ}
  (f : Fin m → (EuclideanSpace ℝ (Fin n) → WithTop ℝ)) (t : Fin m → ℝ)
  (hf_convex : ∀ i, InConvRn (f i)) (ht_positive : ∀ i, (t i) > 0)
  : let g := fun x => ∑ i, (t i) * ((f i) x)
    InConvRn g
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.1.1.ii -/
lemma FCA_chap_B_2_1_1_ii {n : ℕ} {m : ℕ}
  (f : Fin m → (EuclideanSpace ℝ (Fin n) → WithTop ℝ)) (t : Fin m → ℝ)
  (hf_closedconvex : ∀ i, InClosedConvRn (f i)) (ht_positive : ∀ i, (t i) > 0)
  : let g := fun x => ∑ i, (t i) * ((f i) x)
    InClosedConvRn g
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.1.2.i -/
lemma FCA_chap_B_2_1_2_i {n : ℕ}
  (J : Set ℕ) (f : ℕ → (EuclideanSpace ℝ (Fin n) → WithTop ℝ))
  (hf_convex : ∀ j ∈ J, ConvexOn ℝ Set.univ (f j)) (hx₀ : ∃ x₀, sSup {y | ∃ j, (j ∈ J) ∧ ((f j) x₀ = y)} < ⊤)
  : let g := fun x => sSup {y | ∃ j, (j ∈ J) ∧ ((f j) x = y)}
    InConvRn g
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.1.2.ii -/
lemma FCA_chap_B_2_1_2_ii {n : ℕ}
  (J : Set ℕ) (f : ℕ → (EuclideanSpace ℝ (Fin n) → WithTop ℝ))
  (hf_convex : ∀ j ∈ J, ConvexOn ℝ Set.univ (f j)) (hf_closed : ∀ j ∈ J, ∀ x, (lscHull (f j)) x = (f j) x)
  (hx₀ : ∃ x₀, sSup {y | ∃ j, (j ∈ J) ∧ ((f j) x₀ = y)} < ⊤)
  : let g := fun x => sSup {y | ∃ j, (j ∈ J) ∧ ((f j) x = y)}
    InClosedConvRn g
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.1.4.i -/
lemma FCA_chap_B_2_1_4_i {m n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (A : AffineMap ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
  (hf_convex : InConvRn f) (hf_nonempty : (Set.range A) ∩ (effDom (liftWithTop f)) ≠ ∅)
  : let g := fun x => f (A x)
    InConvRn g
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.1.4.ii -/
lemma FCA_chap_B_2_1_4_ii {m n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (A : AffineMap ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
  (hf_convex : InClosedConvRn f) (hf_nonempty : (Set.range A) ∩ (effDom (liftWithTop f)) ≠ ∅)
  : let g := fun x => f (A x)
    InClosedConvRn g
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.2.1 -/
lemma FCA_chap_B_2_2_1 {m n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (hf_convex : InConvRn f)
  : InConvRn (fun x => (perspective f) (x 0) (Matrix.vecTail x))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.2.2 -/
lemma FCA_chap_B_2_2_2 {m n : ℕ} [NeZero n]
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x' : EuclideanSpace ℝ (Fin n))
  (hf_convex : InClosedConvRn f) (hx : x' ∈ intrinsicInterior ℝ (effDom (liftWithTop f)))
  : let pers := fun z => (perspective f) (z 0) (Matrix.vecTail z)
    let x : EuclideanSpace ℝ (Fin (n + 1)) := (Matrix.vecCons 1 x')
  ∀ (z : EuclideanSpace ℝ (Fin (n + 1))), (z 0 ≥ 0) →
    Filter.Tendsto (fun α => pers (z + α • (x - z))) (𝓝[>] 0) (𝓝 (lscHull pers z))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.3.3  -/
lemma FCA_chap_B_2_3_3 {m n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_convex : InConvRn f₁ ∧ InConvRn f₂)
  (h_common_affine_minorant : ∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ),
                              (∀ x, f₁ x ≥ (inner ℝ s x) - b) ∧ (∀ x, f₂ x ≥ (inner ℝ s x) - b))
  : InProperConvRn (infimalConv f₁ f₂)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Theorem 2.4.2 -/
lemma FCA_chap_B_2_4_2 {m n : ℕ}
  (A : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)))
  (g : EuclideanSpace ℝ (Fin m) → WithBot (WithTop ℝ))
  (hg_convex : InProperConvRn g) (hg_bounded : ∀ x, sInf (Set.image g {y | A y = x}) > ⊥)
  : InProperConvRn (imageFun A g)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Corollary 2.4.3 -/
lemma FCA_chap_B_2_4_3 {p n : ℕ}
  (phi : EuclideanSpace ℝ (Fin p) → WithBot (WithTop ℝ))
  (c : (Fin n) → (EuclideanSpace ℝ (Fin p) → WithBot (WithTop ℝ)))
  (h_phi_convex : InProperConvRn phi) (hc_convex : ∀ j, InProperConvRn (c j))
  (h_nonempty_dom : Set.Nonempty (effDom phi ∩ (⋂ j, effDom (c j))))
  (h_noninf_val : ∀ x, (valueFun phi c x) > ⊥)
  : InProperConvRn (valueFun phi c)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Corollary 2.4.5 -/
lemma FCA_chap_B_2_4_5 {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin (n + m)) → WithBot (WithTop ℝ))
  (hg_convex : InProperConvRn g)
  (hg_bounded : ∀ (x : EuclideanSpace ℝ (Fin n)), sInf (Set.image g {z : EuclideanSpace ℝ (Fin (n + m)) | ∃ (y : EuclideanSpace ℝ (Fin m)), z = Fin.append x y}) > ⊥)
  : InProperConvRn (marginalFun g)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.5.1 -/
lemma FCA_chap_B_2_5_1 {n : ℕ}
  (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hg_minorized : ∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x, g x ≥ inner ℝ s x - b)
  : let f₁ := fun x => sInf {r : WithTop ℝ | ∃ z ∈ convexHull ℝ (epigraph g), z.1 = x ∧ z.2 = r}
    let f₂ := fun x => sSup {z : WithTop ℝ | ∃ (h : EuclideanSpace ℝ (Fin n) → WithTop ℝ),
                                               (InConvRn h) ∧ (Minorizes h g) ∧ (z = h x)}
    let f₃ := fun x => sInf (⋃ k, {z | ∃ (α : EuclideanSpace ℝ (Fin k))
                                          (x₀ : (Fin k) → EuclideanSpace ℝ (Fin n)),
                                          (α ∈ Δκ k) ∧ (∀ j, x₀ j ∈ effDom (liftWithTop g)) ∧
                                          (x = ∑ j, (α j) • (x₀ j)) ∧
                                          (z = ∑ j, (α j) • g (x₀ j))})
    (InConvRn f₁) ∧ (InConvRn f₂) ∧ (InConvRn f₃) ∧
    (∀ x, (f₁ x = f₂ x) ∧ (f₂ x = f₃ x))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section B, Proposition 2.5.2 -/
lemma FCA_chap_B_2_5_2 {n : ℕ}
  (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hg_minorized : ∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x, g x ≥ inner ℝ s x - b)
  : let f₁ := fun x => sInf {r : WithTop ℝ | ∃ z ∈ closure (convexHull ℝ (epigraph g)), z.1 = x ∧ z.2 = r}
    let f₂ := fun x => sSup {z : WithTop ℝ | ∃ (h : EuclideanSpace ℝ (Fin n) → WithTop ℝ),
                                               (InClosedConvRn h) ∧ (Minorizes h g) ∧ (z = h x)}
    let f₃ := fun x => sSup {z : WithTop ℝ | ∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ),
                                               (∀ y, inner ℝ s y - b ≤ g y) ∧ (z = inner ℝ s x - b)}
    (InClosedConvRn f₁) ∧ (InClosedConvRn f₂) ∧ (InClosedConvRn f₃) ∧
    (∀ x, (f₁ x = f₂ x) ∧ (f₂ x = f₃ x))
  := by sorry
