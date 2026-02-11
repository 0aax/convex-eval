import Mathlib
import Aesop

import ConvexEval.definitions

open BigOperators Real Nat Topology Rat

/- Hiriart-Urruty Lemarechal, Proposition 1.2.1 -/
lemma CAMA_chap_3_1_2_1 {n : ℕ}
  (J : Set ℕ)
  (C : ℕ → Set (EuclideanSpace ℝ (Fin n)))
  (hC : ∀ i, Convex ℝ (C i)) :
  Convex ℝ (⋂ (j : ℕ) (_ : j ∈ J), (C j)) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 1.2.4 -/
lemma CAMA_chap_3_1_2_4 {m n : ℕ}
  (A : AffineMap ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (D : Set (EuclideanSpace ℝ (Fin m)))
  (hC : Convex ℝ C)
  (hD : Convex ℝ D) :
  Convex ℝ (Set.image A C) ∧
  (Convex ℝ (Set.preimage A D)) := by
  sorry

/- Hiriart-Urruty Lemarechal Proposition 1.2.7 -/
lemma CAMA_chap_3_1_2_7 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC : Convex ℝ C) :
  Convex ℝ (interior C) ∧ Convex ℝ (closure C):= by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 1.3.3 -/
lemma CAMA_chap_3_1_3_3 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) :
  (Convex ℝ C) ↔ (∀ z ∈ (conv C), z ∈ C) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 1.3.4 -/
lemma CAMA_chap_3_1_3_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) :
  (convexHull ℝ C) = (conv C) := by
  sorry

/- Hiriart-Urruty Lemarechal, lemma 1.3.6 (Caratheodory) -/
lemma CAMA_chap_3_1_3_6 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n))) :
  ∀ x ∈ (convexHull ℝ S),
  ∃ (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin (n + 1))),
  (∀ i, v i ∈ S) ∧ (a ∈ Δκ (n + 1)) ∧ (x = ∑ i, a i • v i) := by
  sorry

/- Hiriart-Urruty Lemarechal, lemma 1.4.3 -/
lemma CAMA_chap_3_1_4_3 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n))) :
  (Bornology.IsBounded S → Bornology.IsBounded (convexHull ℝ S)) ∧
  (IsCompact S → IsCompact (convexHull ℝ S)) := by
  sorry

/- Hiriart-Urruty Lemarechal, lemma 2.1.3 -/
lemma CAMA_chap_3_2_1_3 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC₀ : Nonempty C)
  (hC₁ : Convex ℝ C) :
  (Set.Nonempty (intrinsicInterior ℝ C)) ∧
  (Module.finrank ℝ (affineSpan ℝ C).direction) =
  (Module.finrank ℝ (affineSpan ℝ (intrinsicInterior ℝ C)).direction) := by
  sorry

/- Hiriart-Urruty Lemarechal, Lemma 2.1.6 -/
lemma CAMA_chap_3_2_1_6 {n : ℕ}
  (x₁ : EuclideanSpace ℝ (Fin n))
  (x₂ : EuclideanSpace ℝ (Fin n))
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C)
  (hx₁ : x₁ ∈ closure C)
  (hx₂ : x₂ ∈ (intrinsicInterior ℝ C)) :
  {v : EuclideanSpace ℝ (Fin n) | ∃ (α : ℝ), (0 ≤ α) ∧ (α < 1) ∧
                                  (v = α • x₁ + (1-α) • x₂)} ⊆ intrinsicInterior ℝ C := by
  sorry

/- Hiriart-Urruty Lemarechal, Lemma 2.1.8 -/
lemma CAMA_chap_3_2_1_8 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C) :
  (closure (intrinsicInterior ℝ C) = closure C) ∧
  (intrinsicInterior ℝ (closure C) = intrinsicInterior ℝ C) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.1.10 -/
lemma CAMA_chap_3_2_1_10 {n : ℕ}
  (C₁ : Set (EuclideanSpace ℝ (Fin n)))
  (C₂ : Set (EuclideanSpace ℝ (Fin n)))
  (hC₁ : Convex ℝ C₁)
  (hC₂ : Convex ℝ C₂)
  (hC : Set.Nonempty (intrinsicInterior ℝ C₁ ∩ intrinsicInterior ℝ C₂)) :
  (intrinsicInterior ℝ (C₁ ∩ C₂) = intrinsicInterior ℝ C₁ ∩ intrinsicInterior ℝ C₂) ∧
  (closure (C₁ ∩ C₂) = closure C₁ ∩ closure C₂):= by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.1.12 -/
lemma CAMA_chap_3_2_1_12 {n : ℕ} {m : ℕ}
  (A : AffineMap ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (D : Set (EuclideanSpace ℝ (Fin m)))
  (hC : Convex ℝ C)
  (hD₀ : Convex ℝ D)
  (hD₁ : Set.Nonempty (Set.preimage A (intrinsicInterior ℝ D))) :
  (intrinsicInterior ℝ (Set.image A C) = Set.image A (intrinsicInterior ℝ C)) ∧
  (intrinsicInterior ℝ (Set.preimage A D) = Set.preimage A (intrinsicInterior ℝ D)) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.2.1 -/
lemma CAMA_chap_3_2_2_1 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x₁ x₂ : EuclideanSpace ℝ (Fin n))
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hx₁ : x₁ ∈ C)
  (hx₂ : x₂ ∈ C) :
  (AsymptoticCone C x₁) = (AsymptoticCone C x₂) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.2.3 -/
lemma CAMA_chap_3_2_2_3 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  (IsCompact C) ↔ ∀ x ∈ C, (AsymptoticCone C x) = {0} := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.3.3 -/
lemma CAMA_chap_3_2_3_3 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC₀ : Set.Nonempty C)
  (hC₁ : Convex ℝ C)
  (hC₂ : IsCompact C) :
  Set.Nonempty (Set.extremePoints ℝ C) := by
  sorry

/- Hiriart-Urruty Lemarechal, lemma 2.3.4 (Minkowski) -/
lemma CAMA_chap_3_2_3_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC₀ : Set.Nonempty C)
  (hC₁ : Convex ℝ C)
  (hC₂ : IsCompact C) :
  C = convexHull ℝ (Set.extremePoints ℝ C) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.3.7 -/
lemma CAMA_chap_3_2_3_7 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (F : Set (EuclideanSpace ℝ (Fin n)))
  (hF : Face C F)
  (hC₀ : Set.Nonempty C)
  (hC₁ : Convex ℝ C) :
  ∀ (x : EuclideanSpace ℝ (Fin n)) (_ : x ∈ (Set.extremePoints ℝ F)),
  x ∈ (Set.extremePoints ℝ C) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.4.3 -/
lemma CAMA_chap_3_2_4_3 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (F : Set (EuclideanSpace ℝ (Fin n)))
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C)
  (hF : IsExposedFace C F) :
  Face C F := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 2.4.6 (max) -/
lemma CAMA_chap_3_2_4_6 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (s : EuclideanSpace ℝ (Fin n))
  (hC₀ : IsCompact C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  (sSup (Set.image (fun x ↦ inner ℝ s x) C) =
  sSup (Set.image (fun x ↦ inner ℝ s x) (Set.extremePoints ℝ C))) ∧
  (Argmax (fun x ↦ inner ℝ s x) C =
  convexHull ℝ (Argmax (fun x ↦ inner ℝ s x) (Set.extremePoints ℝ C))) := by
  sorry

/- Hiriart-Urruty Lemarechal, lemma 3.1.1 -/
lemma CAMA_chap_3_3_1_1 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x y : EuclideanSpace ℝ (Fin n))
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C)
  (hy : y ∈ C) :
  y = pC x C hC₀ hC₁ hC₂ ↔ ∀ z ∈ C, inner ℝ (x - y) (z - y) ≤ 0 := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 3.1.3 -/
lemma CAMA_chap_3_3_1_3 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x₁ x₂ : EuclideanSpace ℝ (Fin n))
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  ‖(pC x₁ C hC₀ hC₁ hC₂) - (pC x₂ C hC₀ hC₁ hC₂)‖ ^ 2
  ≤ inner ℝ ((pC x₁ C hC₀ hC₁ hC₂) - (pC x₂ C hC₀ hC₁ hC₂)) (x₁ - x₂) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 3.2.3 -/
lemma CAMA_chap_3_3_2_3 {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (x y : EuclideanSpace ℝ (Fin n))
  (hK₀ : IsConvexCone K)
  (hK₁ : IsClosed K)
  (hK₂ : Set.Nonempty K) :
  y = pC x K hK₁ (convexCone_isConvex hK₀) hK₂ ↔
  (y ∈ K) ∧ (x - y ∈ PolarCone K) ∧ (inner ℝ (x - y) y = 0) := by
  sorry

/- Hiriary-Urruty Lemarechal, lemma 3.2.5 (J.-J. Moreau) -/
lemma CAMA_chap_3_3_2_5 {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (x x₁ x₂ : EuclideanSpace ℝ (Fin n))
  (hK₀ : IsConvexCone K)
  (hK₁ : IsClosed K)
  (hK₂ : Set.Nonempty K) :
  let K' := (PolarCone K)
  x = x₁ + x₂ ∧ x₁ ∈ K ∧ x₂ ∈ K' ∧ inner ℝ x₁ x₂ = 0 ↔
  x₁ = pC x K hK₁ (convexCone_isConvex hK₀) hK₂ ∧
  x₂ = pC x K' polarCone_isClosed polarCone_isConvex polarCone_isNonempty := by
  sorry

/- Hiriart-Urruty Lemarechal, lemma 4.1.1 -/
lemma CAMA_chap_3_4_1_1 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hx : x ∉ C) :
  ∃ (s : EuclideanSpace ℝ (Fin n)), (s ≠ 0) ∧ (inner ℝ s x > ⨆ y ∈ C, inner ℝ s y) := by
  sorry

/- Hiriart-Urruty Lemarechal, Corollary 4.1.3 (Strict separation of Convex ℝ sets ) -/
lemma CAMA_chap_3_4_1_3 {n : ℕ}
  (C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)))
  (hC₁ : Set.Nonempty C₁)
  (hC₁' : IsClosed C₁)
  (hC₁'' : Convex ℝ C₁)
  (hC₂ : Set.Nonempty C₂)
  (hC₂' : IsClosed C₂)
  (hC₂'' : Convex ℝ C₂)
  (hI : (C₁ ∩ C₂) = ∅)
  (h_bounded : Bornology.IsBounded C₂) :
  ∃ (s : EuclideanSpace ℝ (Fin n)),
  ⨆ y ∈ C₁, inner ℝ s y < ⨅ y ∈ C₂, inner ℝ s y := by
  sorry

/- Hiriart Urruty Lemarechal, lemma 4.1.4 (Proper separation of Convex ℝ sets) -/
lemma CAMA_chap_3_4_1_4 {n : ℕ}
  (C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)))
  (hC₁ : Set.Nonempty C₁)
  (hC₁' : Convex ℝ C₁)
  (hC₂ : Set.Nonempty C₂)
  (hC₂' : Convex ℝ C₂)
  (hI : (intrinsicInterior ℝ C₁ ∩ intrinsicInterior ℝ C₂) = ∅) :
  ∃ (s : EuclideanSpace ℝ (Fin n)),
  ⨆ y₁ ∈ C₁, inner ℝ s y₁ ≤ ⨅ y₂ ∈ C₂, inner ℝ s y₂ ∧
  ⨅ y₁ ∈ C₁, inner ℝ s y₁ < ⨆ y₂ ∈ C₂, inner ℝ s y₂ := by
  sorry

/- Hiriart-Urruty Lemarechal, Lemma 4.2.1 -/
lemma CAMA_chap_3_4_2_1 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (hC_convex : Convex ℝ C)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hx : x ∈ frontier C) :
  ∃ (r : ℝ) (s : EuclideanSpace ℝ (Fin n)), SupportingHyperplaneAt s x r C := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 4.2.3 -/
lemma CAMA_chap_3_4_2_3 {n : ℕ}
  (S C : Set (EuclideanSpace ℝ (Fin n)))
  (hC : C = convexHull ℝ S) :
  ∀ x ∈ C ∩ (frontier C),
  ∃ (v : Fin n → EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin n)),
  (∀ i, v i ∈ S) ∧ (a ∈ Δκ n) ∧ (x = ∑ i, a i • v i) := by
  sorry

/- Hiriary-Urruty Lemarechal, lemma 4.2.4 -/
lemma CAMA_chap_3_4_2_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC₀ : Convex ℝ C)
  (hC₁ : Set.Nonempty C)
  (hC₂ : C ⊂ Set.univ) :
  closure C = ⋂ v ∈ (I_C C), Hyperplane v.1 v.2 := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 4.2.7 -/
lemma CAMA_chap_3_4_2_7 {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (hK_convex_cone : IsConvexCone K)
  (hK_nonempty : Set.Nonempty K) :
  PolarCone (PolarCone K) = closure K := by
  sorry

/- Hiriart-Urruty Lemarechal, Lemma 4.3.1 (Farkas I) -/
lemma CAMA_chap_3_4_3_1 {m n : ℕ}
  (b : EuclideanSpace ℝ (Fin n))
  (s : Fin m → EuclideanSpace ℝ (Fin n)) :
  {x : EuclideanSpace ℝ (Fin n) | ∀ j, inner ℝ (s j) x ≤ 0} ⊆
  {x : EuclideanSpace ℝ (Fin n) | inner ℝ b x ≤ 0} ↔ b ∈ cone s := by
  sorry

/- Hiriary-Urruty Lemarechal, Lemma 4.3.2 (Farkas II) -/
lemma CAMA_chap_3_4_3_2 {m n : ℕ}
  (b : EuclideanSpace ℝ (Fin n))
  (s : Fin m → EuclideanSpace ℝ (Fin n)) :
  let P := b ∈ cone s
  let Q := ∃ (x : EuclideanSpace ℝ (Fin n)), (inner ℝ b x > 0) ∧ (∀ j, inner ℝ (s j) x ≤ 0)
  (P ∨ Q) ∧ ¬(P ∧ Q) := by
  sorry

/- Hiriart-Urruty Lemarechal, Lemma 4.3.3 (Farkas III) -/
lemma CAMA_chap_3_4_3_3 {m n : ℕ}
  (s : Fin m → EuclideanSpace ℝ (Fin n)) :
  IsClosed (cone s) := by
  sorry

-- /- Hiriart-Urruty Lemarechal, lemma 4.3.4 (Generalized Farkas) -/
-- lemma CAMA_chap_3_4_3_4 {m n : ℕ}
--   (b : EuclideanSpace ℝ (Fin n) × ℝ) (J : Set ℕ)
--   (s : ℕ → EuclideanSpace ℝ (Fin n) × ℝ)
--   : ∃ (x : EuclideanSpace ℝ (Fin n)), ∀ j ∈ J, inner ℝ (s j).1 x ≤ (s j).2
--   → (∀ (x : EuclideanSpace ℝ (Fin n)), (∀ j ∈ J, inner ℝ (s j).1 x ≤ (s j).2) → (inner ℝ b.1 x ≤ b.2)
--   ↔ b ∈ ConvexCone.span )
--   := by sorry

/- Hiriart-Urruty Lemarechal, Proposition 5.1.2 -/
lemma CAMA_chap_3_5_1_2 {n : ℕ}
  (d : EuclideanSpace ℝ (Fin n))
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) :
  IsTangent d S x ↔
  ∃ (dk : ℕ → EuclideanSpace ℝ (Fin n)), ∃ (tk : ℕ → ℝ),
  (Filter.Tendsto dk Filter.atTop (𝓝 d)) ∧
  (Filter.Tendsto tk Filter.atTop (𝓝 0)) ∧
  (∀ i, tk i > 0) ∧
  (∀ k, x + (tk k) • (dk k) ∈ S) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 5.1.3 -/
lemma CAMA_chap_3_5_1_3 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) :
  IsClosed (TangentCone x S) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 5.2.1 -/
lemma CAMA_chap_3_5_2_1 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (hx_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  TangentCone x C = closure (GenCone (translate_set C x)) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 5.2.4 -/
lemma CAMA_chap_3_5_2_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (hX_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  NormalCone x C = PolarCone (TangentCone x C) := by
  sorry

/- Hiriart-Urruty Lemarechal, Corollary 5.2.5 -/
lemma CAMA_chap_3_5_2_5 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (hx_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  TangentCone x C = PolarCone (NormalCone x C) := by
  sorry

/- Hiriart-Urruty Lemarechal, Proposition 5.3.1 -/
lemma CAMA_chap_3_5_3_1 {n : ℕ}
  (x : EuclideanSpace ℝ (Fin n))
  (C₁ : Set (EuclideanSpace ℝ (Fin n)))
  (C₂ : Set (EuclideanSpace ℝ (Fin n)))
  (hC₁₀ : Set.Nonempty C₁)
  (hC₁₁ : IsClosed C₁)
  (hC₁₂ : Convex ℝ C₁)
  (hC₂₀ : Set.Nonempty C₂)
  (hC₂₁ : IsClosed C₂)
  (hC₂₂ : Convex ℝ C₂) :
  x ∈ C₁ ∩ C₂ → TangentCone x (C₁ ∩ C₂) ⊆ TangentCone x C₁ ∩ TangentCone x C₂ ∧
  NormalCone x (C₁ ∩ C₂) ⊇ set_add (NormalCone x C₁) (NormalCone x C₂) := by
  sorry

-- /- Hiriart-Urruty Lemarechal, Proposition 5.3.1 (iii.a) -/
-- lemma CAMA_chap_3_5_3_1_iii_a {n : ℕ}
--   (x : EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
--   (y₀ : EuclideanSpace ℝ (Fin n))
--   (A₀ : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)))
--   (hC_nonempty : Set.Nonempty C) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
--   (hx : x ∈ C)
--   : let A := fun z => A₀ z + y₀
--   TangentCone (A x) (Set.image A C) = closure (Set.image A₀ (TangentCone x C))
--   := by sorry

/- Hiriart-Urruty Lemarechal, Proposition 5.3.3 -/
lemma CAMA_chap_3_5_3_3 {n : ℕ}
  (x : EuclideanSpace ℝ (Fin n))
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (s : EuclideanSpace ℝ (Fin n))
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hx_in_C : x ∈ C) :
  List.TFAE [
    s ∈ NormalCone x C,
    (inner ℝ s x) = ⨆ y ∈ C, inner ℝ s y,
    x = pC (x + s) C hC_closed hC_convex hC_nonempty
  ] := by
  sorry
