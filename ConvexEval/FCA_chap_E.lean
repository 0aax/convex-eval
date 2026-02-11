import Mathlib
import Aesop
import ConvexEval.definitions

open BigOperators Real Nat Topology Rat

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.1.2 -/
lemma FCA_chap_E_1_1_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) :
  InClosedConvRn (Conjugate f) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Example 1.2.1.i -/
lemma FCA_chap_E_1_2_1_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) :
  Conjugate f = fun s => sSup {z : WithTop ℝ | ∃ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), (z = inner ℝ s x - r) ∧ ((x, r) ∈ epigraph (liftWithToptoEReal f))} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Example 1.2.1.ii -/
lemma FCA_chap_E_1_2_1_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) :
  let f_conj := fun s => Conjugate f s
  let f_epi_supportfun := fun (s : EuclideanSpace ℝ (Fin n)) (u : ℝ) => SupportFun {z | (vecHead z, vecLast z) ∈ (epigraph (liftWithToptoEReal f))} (Fin.snoc s (-u))
  let f_dom_supportfun := fun s => SupportFun {z | z ∈ effDom (liftWithToptoEReal f)} s
  f_epi_supportfun = (fun s u =>
    if u > 0 then u • f_conj (u⁻¹ • s)
    else if u = 0 then f_dom_supportfun s
    else ⊤
  ) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.2.2 -/
lemma FCA_chap_E_1_2_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f) (hf_closed_convex : InClosedConvRn f)
  (hx₀ : f x₀ ≠ ⊤) :
  let f_conj := fun s => Conjugate f s
  let f_epi_supportfun := fun (s : EuclideanSpace ℝ (Fin n)) (u : ℝ) =>
                               SupportFun {z | (vecHead z, vecLast z) ∈ (epigraph (liftWithToptoEReal f))} (Fin.snoc s (-u))
  let f_dom_supportfun := fun s => SupportFun {z | z ∈ effDom (liftWithToptoEReal f)} s
  let f_conj_asympfun := fun s => AsymptoticFun f_conj x₀ s
  ∀ s, (f_epi_supportfun s 0 = f_dom_supportfun s) ∧ (f_dom_supportfun s = f_conj_asympfun s) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.i -/
lemma FCA_chap_E_1_3_1_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (r : ℝ) (hf_nondegenerate : IsNondegenerate f) :
  let g := fun x => f x + r
  let f_conj := fun s => Conjugate f s
  let g_conj := fun s => Conjugate g s
    ∀ s, g_conj s = f_conj s - r := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.ii -/
lemma FCA_chap_E_1_3_1_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (t : ℝ)
  (hf_nondegenerate : IsNondegenerate f) (ht_pos : t > 0)
  : let g := fun x => t • f x
    let f_conj := fun s => Conjugate f s
    let g_conj := fun s => Conjugate g s
    ∀ s, g_conj s = t • f_conj (t⁻¹ • s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.iii -/
lemma FCA_chap_E_1_3_1_iii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (t : ℝ)
  (hf_nondegenerate : IsNondegenerate f) (ht_nonzero : t ≠ 0)
  : let g := fun x => f (t • x)
    let f_conj := fun s => Conjugate f s
    let g_conj := fun s => Conjugate g s
    ∀ s, g_conj s = f_conj (t⁻¹ • s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.iv -/
lemma FCA_chap_E_1_3_1_iv {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (A : (EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n)))
  (hf_nondegenerate : IsNondegenerate f)
  : let g := fun x => f (A x)
    let A_adjoint_inverse : (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
                            (A.symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).adjoint
    ∀ s, Conjugate g s = Conjugate f (A_adjoint_inverse s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.v -/
lemma FCA_chap_E_1_3_1_v {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : let g := fun x => f (x - x₀)
    ∀ s, Conjugate g s = Conjugate f s + inner ℝ s x₀
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.vi -/
lemma FCA_chap_E_1_3_1_vi {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (s₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : let g := fun x => f x + inner ℝ s₀ x
    ∀ s, Conjugate g s = Conjugate f (s - s₀)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.vii -/
lemma FCA_chap_E_1_3_1_vii {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f₁ ∧ IsNondegenerate f₂)
  (hf₁_minorizes : Minorizes f₁ f₂)
  : Minorizes (Conjugate f₂) (Conjugate f₁)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.1.viii -/
lemma FCA_chap_E_1_3_1_viii {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (α : ℝ)
  (hf_nondegenerate : IsNondegenerate f₁ ∧ IsNondegenerate f₂)
  : Set.Nonempty (effDom (liftWithToptoEReal f₁) ∩ effDom (liftWithToptoEReal f₂)) → α ∈ Set.Ioo 0 1 →
    Minorizes (Conjugate (fun x => α • f₁ x + (1 - α) • f₂ x))
              (α • (Conjugate f₁) + (1 - α) • (Conjugate f₂))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.2 -/
lemma FCA_chap_E_1_3_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (H : Subspace ℝ (EuclideanSpace ℝ (Fin n)))
  (hf_nondegenerate : IsNondegenerate f)
  : let pH : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => Submodule.orthogonalProjection H x
    let g := fun x => f x + (Indicator H) x
    ∀ s, Conjugate g s = Conjugate (f ∘ pH) (pH s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.4 -/
lemma FCA_chap_E_1_3_4 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (V : Subspace ℝ (EuclideanSpace ℝ (Fin n)))
  (hf_nondegenerate : IsNondegenerate f) (hV_contains_affdom : affineSpan ℝ (effDom (liftWithToptoEReal f)))
  : let U := Vᗮ
    let pV : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => Submodule.orthogonalProjection V x
    let pU : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => Submodule.orthogonalProjection U x
    ∀ z ∈ affineSpan ℝ (effDom (liftWithToptoEReal f)), ∀ s,
    Conjugate f s = inner ℝ (pU s) z + Conjugate f (pV s)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.3.5 -/
lemma FCA_chap_E_1_3_5 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (hf_nondegenerate : IsNondegenerate f)
  : epigraph (liftWithToptoEReal (Biconjugate f)) = closure (convexHull ℝ (epigraph (liftWithToptoEReal f)))
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.3.6.i -/
lemma FCA_chap_E_1_3_6_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hg : (Minorizes (Biconjugate f) g) ∧ (Minorizes g f))
  : ∀ s, Conjugate g s = Conjugate f s
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.3.6.ii -/
lemma FCA_chap_E_1_3_6_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  : (Biconjugate f = f) ↔ (InClosedConvRn f)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.8 -/
lemma FCA_chap_E_1_3_8 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) (hf_coercive : IsOneCoerciveFun f)
  : ∀ s, Conjugate f s < ⊤
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.9.i -/
lemma FCA_chap_E_1_3_9_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : x₀ ∈ interior (effDom (liftWithToptoEReal f)) → IsZeroCoerciveFun (fun x => Conjugate f x - inner ℝ x₀ x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Proposition 1.3.9.ii -/
lemma FCA_chap_E_1_3_9_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f)
  : ∀ x, f x ≠ ⊤ → IsOneCoerciveFun (Conjugate f)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Remark 1.3.10.i -/
lemma FCA_chap_E_1_3_10_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f) (hf_closed_convex : InClosedConvRn f)
  : x₀ ∈ interior (effDom (liftWithToptoEReal f)) ↔ IsZeroCoerciveFun (fun x => Conjugate f x - inner ℝ x₀ x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Remark 1.3.10.ii -/
lemma FCA_chap_E_1_3_10_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (hf_nondegenerate : IsNondegenerate f) (hf_closed_convex : InClosedConvRn f)
  : ∀ (x : EuclideanSpace ℝ (Fin n)), x ∈ (effDom (liftWithToptoEReal f)) ↔ IsOneCoerciveFun (Conjugate f)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.1 -/
lemma FCA_chap_E_1_4_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x s : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : s ∈ SubdifferentialAt f x ↔ (Conjugate f s) + f x - (inner ℝ s x) = 0
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.2 -/
lemma FCA_chap_E_1_4_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : InConvRn f)
  : x ∈ intrinsicInterior ℝ (effDom (liftWithToptoEReal f)) → Set.Nonempty (SubdifferentialAt f x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.3.i -/
lemma FCA_chap_E_1_4_3_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : Set.Nonempty (SubdifferentialAt f x) → Biconjugate f x = f x
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.3.ii -/
lemma FCA_chap_E_1_4_3_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : (Minorizes (Biconjugate f) g) ∧ (Minorizes g f) ∧ (g x = f x) → (SubdifferentialAt g x) = (SubdifferentialAt f x)
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Theorem 1.4.3.iii -/
lemma FCA_chap_E_1_4_3_iii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x s : EuclideanSpace ℝ (Fin n))
  (hf_nondegenerate : IsNondegenerate f)
  : s ∈ SubdifferentialAt f x → x ∈ SubdifferentialAt (Conjugate f) s
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Corollary 1.4.4 -/
lemma FCA_chap_E_1_4_4 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x s : EuclideanSpace ℝ (Fin n))
  (hf_closed_convex : InClosedConvRn f)
  : List.TFAE [
    f x + Conjugate f s - inner ℝ s x = 0,
    s ∈ SubdifferentialAt f x,
    x ∈ SubdifferentialAt (Conjugate f) s
  ]
  := by sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Corollary 2.1.1 -/
lemma FCA_chap_E_2_1_1 {m n : ℕ}
  (g : EuclideanSpace ℝ (Fin m) → WithTop ℝ)
  (A : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)))
  (hg_nondegenerate : IsNondegenerate g)
  (h_nonempty_domain : Set.Nonempty ((Im A.adjoint) ∩ effDom (liftWithToptoEReal (Conjugate g))))
  : let h := fun x => sInf (Set.image g {y | A y = x})
    ∀ s, Conjugate h s = Conjugate g (A.adjoint s)
  := by sorry

-- /- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section E, Corollary 2.1.3 -/
-- lemma FCA_chap_E_2_1_3 {n : ℕ}
--   (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
--   (hf_not_infinity : ∃ x₁, f₁ x₁ ≠ ⊤ ∧ ∃ x₂, f₂ x₂ ≠ ⊤)
--   (h_nonempty_domain : Set.Nonempty (effDom (Conjugate (liftWTtoEReal f₁)) ∩ effDom (Conjugate (liftWTtoEReal f₂))))
--   : let inf_conv := infimalConv f₁ f₂
--   (IsNondegenerate inf_conv) ∧
--   (∀ s, Conjugate inf_conv s = (Conjugate (liftWTtoEReal f₁) s) + (Conjugate (liftWTtoEReal f₂) s))
--   := by sorry
