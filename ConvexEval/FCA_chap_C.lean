import Mathlib
import Aesop
import ConvexEval.definitions

open BigOperators Real Nat Topology Rat

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 1.1.3 -/
lemma FCA_chap_C_1_1_3 {n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
  let epi := epigraph (liftWithToptoEReal σ)
  (IsSublinear (liftWithToptoEReal σ)) ↔
  (Set.Nonempty epi ∧ Convex ℝ epi ∧ IsCone epi) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 1.1.4 -/
lemma FCA_chap_C_1_1_4 {n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hσ : ∃ x, σ x ≠ ⊤) :
  (IsSublinear (liftWithToptoEReal σ)) ↔
  ((∀ (x₁ x₂ : EuclideanSpace ℝ (Fin n)), ∀ (t₁ t₂ : ℝ),
   t₁ > 0 → t₂ > 0 → σ (t₁ • x₁ + t₂ • x₂) ≤ t₁ • (σ x₁) + t₂ • (σ x₂)) ∨
   ((IsKPosHomogeneous σ 1) ∧ (IsSubadditive σ))) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Corollary 1.1.5 -/
lemma FCA_chap_C_1_1_5 {n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
  (IsSublinear (liftWithToptoEReal σ)) →
  (∀ (x : EuclideanSpace ℝ (Fin n)), σ x + σ (-x) ≥ 0) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Corollary 1.1.6 -/
lemma FCA_chap_C_1_1_6 {m n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (hσ : IsSublinear (liftWithToptoEReal σ))
  (h_eq_0 : ∀ j ∈ Finset.range m, σ (x j) + σ (-1 • (x j)) = 0) :
  let 𝓧 := {v | InSubspaceSpanVec m x v}
  (IsLinearOn 𝓧 σ):= by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Corollary 1.1.7 -/
lemma FCA_chap_C_1_1_7 {m n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hσ : IsSublinear (liftWithToptoEReal σ)) :
  (σ x + σ (-1 • x) = 0) →
  ∀ (y : EuclideanSpace ℝ (Fin n)), σ (x + y) = σ x + σ y := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Corollary 1.2.5 -/
lemma FCA_chap_C_1_2_5 {m n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_origin : 0 ∈ C) :
  let g : EuclideanSpace ℝ (Fin n) → WithTop ℝ := fun x => gauge C x
  List.TFAE [
    (∀ x, g x ≥ 0) ∧ (IsSublinear (liftWithToptoEReal g)) ∧ (IsClosedFun g),
    (∀ x, g x ≠ ⊤) ↔ (0 ∈ interior C)
  ] := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Corollary 1.2.6 -/
lemma FCA_chap_C_1_2_6 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_origin : 0 ∈ C) :
  let g : EuclideanSpace ℝ (Fin n) → WithTop ℝ := fun x => gauge C x
  (IsCompact C) ↔ (∀ x, x ≠ 0 → g x > 0) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 1.3.1 (i) -/
lemma FCA_chap_C_1_3_1_i {n : ℕ}
  (σ₁ σ₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (t₁ t₂ : ℝ)
  (hσ : IsSublinear (liftWithToptoEReal σ₁) ∧ IsSublinear (liftWithToptoEReal σ₂))
  (ht : t₁ > 0 ∧ t₂ > 0) :
  let σ := t₁ • σ₁ + t₂ • σ₂
  (∀ x, σ x ≠ ⊤ → IsSublinear (liftWithToptoEReal σ)) ∧
  (IsClosedFun σ₁ ∧ IsClosedFun σ₂ → ∀ x, σ x ≠ ⊤ →
  IsSublinear (liftWithToptoEReal σ) ∧ IsClosedFun σ):= by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 1.3.1 (ii) -/
lemma FCA_chap_C_1_3_1_ii {n : ℕ}
  (σ : ℕ → (EuclideanSpace ℝ (Fin n) → WithTop ℝ))
  (J : Set ℕ)
  (hσ_sublinear : ∀ j ∈ J, IsSublinear (liftWithToptoEReal (σ j))) :
  let σ' := fun x => sSup (⋃ j ∈ J, {(σ j) x})
  (∀ x, σ' x ≠ ⊤ → IsSublinear (liftWithToptoEReal σ')) ∧
  (∀ j ∈ J, IsClosedFun (σ j) → ∀ x, σ' x ≠ ⊤ →
  IsSublinear (liftWithToptoEReal σ') ∧ IsClosedFun σ') := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 1.3.2 (i) -/
lemma FCA_chap_C_1_3_2_i {n : ℕ}
  (σ : ℕ → (EuclideanSpace ℝ (Fin n) → WithTop ℝ))
  (J : Set ℕ)
  (hσ_sublinear : ∀ j ∈ J, IsSublinear (liftWithToptoEReal (σ j)))
  (hσ_minorized : ∃ (s : EuclideanSpace ℝ (Fin n)), ∃ (b : ℝ),
                  ∀ j ∈ J, ∀ (x : EuclideanSpace ℝ (Fin n)),
                  (σ j) x ≥ (inner ℝ s x) + b) :
  let σ_inf := fun x => sInf (⋃ j ∈ J, {(σ j) x})
  let σ' := lscHull σ_inf
  IsSublinear (liftWithToptoEReal σ') := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 1.3.2 (ii) -/
lemma FCA_chap_C_1_3_2_ii {m n : ℕ}
  (σ : ℕ → (EuclideanSpace ℝ (Fin n) → WithTop ℝ))
  (J : ℕ → ℕ)
  (hσ_sublinear : ∀ i, i ≤ m → IsSublinear (liftWithToptoEReal (σ (J i))))
  (hσ_minorized : ∃ (s : EuclideanSpace ℝ (Fin n)), ∃ (b : ℝ),
                  ∀ i, i ≤ m → ∀ (x : EuclideanSpace ℝ (Fin n)),
                  (σ (J i)) x ≥ (inner ℝ s x) + b) :
  let σ_infconv := multiInfimalConv m σ
  let σ_min := fun x => sInf (⋃ i ∈ Finset.range m, {(σ (J i)) x})
  let σ' := lscHull σ_min
  ∀ x, σ_infconv x = (liftWithToptoEReal σ') x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 1.3.5 -/
lemma FCA_chap_C_1_3_5 {n : ℕ}
  (σk : ℕ → (EuclideanSpace ℝ (Fin n) → ℝ))
  (σ : EuclideanSpace ℝ (Fin n) → ℝ) :
  let d := fun k => DistOnFunctions (σk k) σ
  List.TFAE [
    (∀ x, Filter.Tendsto (fun k => (σk k) x) Filter.atTop (𝓝 (σ x))),
    (∀ (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K →
    TendstoUniformlyOn σk σ Filter.atTop K),
    (Filter.Tendsto d Filter.atTop (𝓝 0))
  ] := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 2.1.2 -/
lemma FCA_chap_C_2_1_2 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (hS : Set.Nonempty S) :
  let support_fun := SupportFun S
  (IsSublinear (liftWithToptoEReal support_fun)) ∧ (IsClosedFun support_fun)
  := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 2.1.3 -/
lemma FCA_chap_C_2_1_3 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (hS : Set.Nonempty S) :
  let support_fun := SupportFun S
  (∀ x, support_fun x ≠ ⊤) ↔
  (Bornology.IsBounded S) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 2.2.1 -/
lemma FCA_chap_C_2_2_1 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (hS : Set.Nonempty S) :
  let sf_S := SupportFun S
  let sf_clS := SupportFun (closure S)
  let sf_coS := SupportFun (convexHull ℝ S)
  let sf_barcoS := SupportFun (closure (convexHull ℝ S))
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  (sf_S x = sf_clS x) ∧
  (sf_clS x = sf_coS x) ∧
  (sf_S x = sf_barcoS x) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 2.2.2 -/
lemma FCA_chap_C_2_2_2 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (s : EuclideanSpace ℝ (Fin n))
  (hS : Set.Nonempty S) :
  let sf_S := SupportFun S
  (s ∈ closure (convexHull ℝ S)) ↔
  (∀ (d : EuclideanSpace ℝ (Fin n)), inner ℝ s d ≤ sf_S d) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 2.2.3 -/
lemma FCA_chap_C_2_2_3 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (s : EuclideanSpace ℝ (Fin n))
  (hS : Set.Nonempty S) :
  let σS := SupportFun S
  ((s ∈ affineHull S) ↔ (∀ d, σS d + σS (-1 • d) = 0 → inner ℝ s d = σS d)) ∧
  ((s ∈ intrinsicInterior ℝ S) ↔ (∀ d, σS d + σS (-1 • d) > 0 → inner ℝ s d < σS d)) ∧
  ((s ∈ interior S) ↔ (∀ d, d ≠ 0 → inner ℝ s d < σS d)):= by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 2.2.4 -/
lemma FCA_chap_C_2_2_4 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S) :
  let σS := SupportFun S
  let Sinfty := AsymptoticCone S x
  PolarCone (closure (effDom (liftWithToptoEReal σS))) = Sinfty := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.1.1 -/
lemma FCA_chap_C_3_1_1 {n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hσ_closed : IsClosedFun σ) (hσ_sublinear : IsSublinear (liftWithToptoEReal σ)) :
  let Sσ := {s | ∀ d, inner ℝ s d ≤ σ d}
  ((∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x, inner ℝ s x + b ≤ σ x)) ∧
  (∀ x, σ x = SupportFun Sσ x) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.1.2 -/
lemma FCA_chap_C_3_1_2 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hS_nonempty : Set.Nonempty S) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
  (hσ_closed : IsClosedFun σ) (hσ_sublinear : IsSublinear (liftWithToptoEReal σ)) :
  let support_fun := SupportFun S
  let S' := {s | ∀ (d : EuclideanSpace ℝ (Fin n)), inner ℝ s d ≤ σ d}
  List.TFAE [
    ∀ (x : EuclideanSpace ℝ (Fin n)), support_fun x = σ x,
    S = S'
  ] := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.1.4 -/
lemma FCA_chap_C_3_1_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n))
  (hC_nonempty : Set.Nonempty C) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
  (hx : x ∈ C) (hd : d ≠ 0) :
  x ∈ DirectionExposingFace C d ↔ d ∈ NormalCone x C := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.2.4 -/
lemma FCA_chap_C_3_2_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_origin : 0 ∈ C) :
  let γC := gauge C
  let C' := {s | ∀ d ∈ C, inner ℝ s d ≤ 1}
  let σC' := SupportFun C'
  ∀ (x : EuclideanSpace ℝ (Fin n)), γC x = σC' x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.2.5 -/
lemma FCA_chap_C_3_2_5 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_origin : 0 ∈ C) :
  let C' := {s | ∀ d ∈ C, inner ℝ s d ≤ 1}
  let σC := SupportFun C
  let γC' := gauge C'
  ∀ (x : EuclideanSpace ℝ (Fin n)), γC' x = σC x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.2.7 -/
lemma FCA_chap_C_3_2_7 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (d s : EuclideanSpace ℝ (Fin n))
  (hC_nonempty : Set.Nonempty C)
  (hC_compact : IsCompact C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ interior C) :
  let C' := {s | ∀ v ∈ C, inner ℝ s v ≤ 1}
  let Hs := {y | inner ℝ s y = 1}
  let Hd := {y | inner ℝ d y = 1}
  List.TFAE [
    ∃ (s' : EuclideanSpace ℝ (Fin n)) (t' : ℝ), (SupportingHyperplaneAt s' d t' C) ∧ (AffineHyperplane s' t' = Hs),
    ∃ (d' : EuclideanSpace ℝ (Fin n)) (t' : ℝ), (SupportingHyperplaneAt d' s t' C) ∧ (AffineHyperplane d' t' = Hd),
    (d ∈ frontier C) ∧ (s ∈ frontier C') ∧ (inner ℝ s d = 1),
    (d ∈ C) ∧ (s ∈ C') ∧ (inner ℝ s d = 1)
  ] := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.3.1 -/
lemma FCA_chap_C_3_3_1 {n : ℕ}
  (S₁ S₂ : Set (EuclideanSpace ℝ (Fin n)))
  (hS_nonempty : Set.Nonempty S₁ ∧ Set.Nonempty S₂)
  (hS_closed : IsClosed S₁ ∧ IsClosed S₂)
  (hS_convex : Convex ℝ S₁ ∧ Convex ℝ S₂) :
  let σ₁ := SupportFun S₁
  let σ₂ := SupportFun S₂
  S₁ ⊆ S₂ ↔ ∀ d, σ₁ d ≤ σ₂ d := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.3.2 (i) -/
lemma FCA_chap_C_3_3_2_i {n : ℕ}
  (S₁ S₂ : Set (EuclideanSpace ℝ (Fin n)))
  (t₁ t₂ : ℝ)
  (hS_nonempty : Set.Nonempty S₁ ∧ Set.Nonempty S₂)
  (hS_closed : IsClosed S₁ ∧ IsClosed S₂)
  (hS_convex : Convex ℝ S₁ ∧ Convex ℝ S₂)
  (ht : t₁ > 0 ∧ t₂ > 0):
  let σ₁ := SupportFun S₁
  let σ₂ := SupportFun S₂
  let S₁' := {x | ∃ s ∈ S₁, x = t₁ • s}
  let S₂' := {x | ∃ s ∈ S₂, x = t₂ • s}
  let S := closure {x | ∃ s₁ ∈ S₁', ∃ s₂ ∈ S₂', x = s₁ + s₂}
  ∀ x, (t₁ • (σ₁ x) + t₂ • (σ₂ x)) = SupportFun S x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.3.2 (ii) -/
lemma FCA_chap_C_3_3_2_ii {n : ℕ}
  (S : ℕ → Set (EuclideanSpace ℝ (Fin n)))
  (J : Set ℕ)
  (hS_nonempty : ∀ j ∈ J, Set.Nonempty (S j))
  (hS_closed : ∀ j ∈ J, IsClosed (S j))
  (hS_convex : ∀ j ∈ J, Convex ℝ (S j)) :
  let σ := fun j => SupportFun (S j)
  let σ_sup := fun x => sSup (⋃ j ∈ J, {(σ j) x})
  let S' := closure (convexHull ℝ (⋃ j ∈ J, S j))
  ∀ x, σ_sup x = SupportFun S' x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.3.2 (iii) -/
lemma FCA_chap_C_3_3_2_iii {n : ℕ}
  (S : ℕ → Set (EuclideanSpace ℝ (Fin n)))
  (J : Set ℕ)
  (hS_closed : ∀ j ∈ J, IsClosed (S j))
  (hS_convex : ∀ j ∈ J, Convex ℝ (S j)) :
  let σ := fun j => SupportFun (S j)
  let S := ⋂ j ∈ J, S j
  let σ_inf := fun x => sInf (⋃ j ∈ J, {(σ j) x})
  let co_σ_inf := fun (x : EuclideanSpace ℝ (Fin n)) => sInf {r : ℝ | (x, r) ∈ epigraph (liftWithToptoEReal σ_inf)}
  S ≠ ∅ → (∀ x, SupportFun S x = lscHull (liftRealtoWT co_σ_inf) x) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.3.3 -/
lemma FCA_chap_C_3_3_3 {m n : ℕ}
  (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
  (s : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (hs : IsScalarProduct s)
  (hS_nonempty : Set.Nonempty S) :
  let A_adj := A.adjoint
  let cl_AS := closure (Set.image A S)
  let σ_clAS := SupportFun cl_AS
  let σ_S_Aadj := fun y => SupportFun S (A_adj y)
  ∀ (y : EuclideanSpace ℝ (Fin m)), σ_clAS y = σ_S_Aadj y := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section C, Proposition 3.3.4 -/
lemma FCA_chap_C_3_3_4 {m n : ℕ}
  (A : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  (s : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
  (S : Set (EuclideanSpace ℝ (Fin m)))
  (hs : IsScalarProduct s)
  (hS_nonempty : Set.Nonempty S) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) :
  let A_star := A.adjoint
  let σ := SupportFun S
  let A_inv := fun d => {p : EuclideanSpace ℝ (Fin m) | A p = d}
  let A_adj_inv_S := {p : EuclideanSpace ℝ (Fin n) | ∃ d ∈ S, A_star p = d}
  let σ_adj_inv := SupportFun A_adj_inv_S
  (∀ (d : EuclideanSpace ℝ (Fin n)), IsMinorizedOn σ (A_inv d)) →
  (∀ (x : EuclideanSpace ℝ (Fin n)), σ_adj_inv x = lscHull (fun v => ImageFunction A σ v) x) := by
  sorry
