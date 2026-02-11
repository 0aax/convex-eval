import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Standard convention where 0*(±∞) = 0
 -/
noncomputable instance : SMul ℝ EReal where
  smul t x := match x with
    | ⊤ => if t = 0 then 0 else ⊤
    | ⊥ => if t = 0 then 0 else ⊥
    | some r => some (t * r)

/- View a `ℝ`-valued function as a `EReal`-valued one. -/
def liftEReal {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) :
  EuclideanSpace ℝ (Fin n) → EReal
  := fun x => (f x : EReal)

/- Lower semi-continuous at -/
noncomputable def lscAt {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop
  := Filter.liminf f (𝓝 x) ≥ f x

/- Epigraph of a function -/
def epigraph {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n) × ℝ)
  := {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ p.2}

/- Sublinear function -/
def IsSublinear {n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  (∀ (x₁ x₂ : EuclideanSpace ℝ (Fin n)), ∀ (t₁ t₂ : ℝ),
  t₁ > 0 → t₂ > 0 → σ (t₁ • x₁ + t₂ • x₂) ≤ t₁ • (σ x₁) + t₂ • (σ x₂))

/- Difference quotient
  * t > 0
-/
noncomputable def differenceQuotient {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x : EuclideanSpace ℝ (Fin n))
  (d : EuclideanSpace ℝ (Fin n)) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

/- Directional derivative -/
noncomputable def directionalDeriv {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x : EuclideanSpace ℝ (Fin n))
  (d : EuclideanSpace ℝ (Fin n)) : EReal :=
  limUnder (𝓝[>] 0) (fun t => differenceQuotient f x d t)

/- If f is convex and finite, then f'(x, ·) is finite -/
noncomputable def realDirectionalDeriv {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (directionalDeriv (liftEReal f) x d).toReal

/- Subdifferential I -/
def SubdifferentialI {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  let f' := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv f x d
  {s : EuclideanSpace ℝ (Fin n) | ∀ d, inner ℝ s d ≤ f' d}

/- Subgradient -/
def IsSubgradientAt {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ SubdifferentialI f x

/- Subdifferential II-/
def SubdifferentialII {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {s : EuclideanSpace ℝ (Fin n) | ∀ y, f y ≥ f x + inner ℝ s (y - x)}

/- Is normal to -/
def IsNormalTo {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ C, inner ℝ s (y - x) ≤ 0

/- Normal cone -/
def normalConeAt {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {s : EuclideanSpace ℝ (Fin n) | IsNormalTo C x s}

/- Sublevel set -/
def sublevelSetFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y : EuclideanSpace ℝ (Fin n) | f y ≤ f x}

/- Exposed face -/
def exposedFace {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (s : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x : EuclideanSpace ℝ (Fin n) | inner ℝ s x = sSup (Set.image (fun y => inner ℝ s y) C)}

/- Infimal convolution -/
noncomputable def infimalConv {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → ℝ)
  (f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : EReal
  := sInf {z : EReal | ∃ y, z = f₁ y + f₂ (x - y)}

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 1.1.2 -/
lemma FCA_HUL_1_1_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  let f' := fun d => directionalDeriv (liftEReal f) x d
  (∀ (z : EuclideanSpace ℝ (Fin n)), f' z < ⊤ ∧ f' z > ⊥) ∧ (IsSublinear f') := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 1.1.6 (i) -/
lemma FCA_HUL_1_1_6_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  let σ := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv (liftEReal f) x d
  let σ' := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv σ 0 d
  ∀ (δ : EuclideanSpace ℝ (Fin n)), σ' δ = σ δ := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 1.1.6 (ii) -/
lemma FCA_HUL_1_1_6_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  let σ := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv (liftEReal f) x d
  let σ' := fun d => directionalDeriv σ 0 d
  ∀ (δ : EuclideanSpace ℝ (Fin n)), (σ δ = σ 0 + σ' δ) ∧ (σ δ = σ' δ) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 1.1.6 (iii) -/
lemma FCA_HUL_1_1_6_iii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  let σ := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv (liftEReal f) x d
  let σ' := fun d => directionalDeriv σ 0 d
  SubdifferentialI σ 0 = SubdifferentialI (liftEReal f) x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 1.2.2 -/
lemma FCA_HUL_1_2_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) (s : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  s ∈ SubdifferentialI (liftEReal f) x ↔ s ∈ SubdifferentialII (liftEReal f) x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 1.3.1 (i) -/
lemma FCA_HUL_1_3_1_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x s : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  let epi_concat := {v : EuclideanSpace ℝ (Fin (n + 1)) |
                         ∃ z ∈ (epigraph (liftEReal f)), v = Fin.snoc z.1 z.2}
  let s' : EuclideanSpace ℝ (Fin (n + 1)) := Fin.snoc s (-1)
  IsSubgradientAt (liftEReal f) x s ↔ IsNormalTo epi_concat (Fin.snoc x (f x)) s' := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 1.3.1 (ii) -/
lemma FCA_HUL_1_3_1_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x s : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  let f' := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv (liftEReal f) x
  let f'_epi := {v : EuclideanSpace ℝ (Fin (n + 1)) |
                     ∃ z ∈ (epigraph (f' x)), v = Fin.snoc z.1 z.2}
  let epi_concat := {v : EuclideanSpace ℝ (Fin (n + 1)) |
                         ∃ z ∈ (epigraph (liftEReal f)), v = Fin.snoc z.1 z.2}
  tangentConeAt ℝ epi_concat (Fin.snoc x (f x)) = f'_epi := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 1.3.2 -/
lemma FCA_HUL_1_3_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf : ConvexOn ℝ Set.univ f) :
  let S := sublevelSetFun (liftEReal f) x
  tangentConeAt ℝ S x ⊆ {d | directionalDeriv (liftEReal f) x d ≤ 0} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 1.3.3 (i) -/
lemma FCA_HUL_1_3_3_i {n : ℕ}
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hg_neg : ∃ (x₀ : EuclideanSpace ℝ (Fin n)), g x₀ < 0):
  closure {z | g z < 0} = {z | g z ≤ 0} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 1.3.3 (ii) -/
lemma FCA_HUL_1_3_3_ii {n : ℕ}
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hg_neg : ∃ (x₀ : EuclideanSpace ℝ (Fin n)), g x₀ < 0):
  {z | g z < 0} = interior {z | g z ≤ 0} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 1.3.3 (iii) -/
lemma FCA_HUL_1_3_3_iii {n : ℕ}
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hg_neg : ∃ (x₀ : EuclideanSpace ℝ (Fin n)), g x₀ < 0):
  frontier {z | g z < 0} = {z | g z = 0} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 1.3.4 -/
lemma FCA_HUL_1_3_4 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_subdiff : Set.Nonempty (SubdifferentialI (liftEReal f) x)) :
  let S := sublevelSetFun (liftEReal f) x
  (tangentConeAt ℝ S x = {d | directionalDeriv (liftEReal f) x d ≤ 0}) ∧
  (interior (tangentConeAt ℝ S x) = {d | directionalDeriv (liftEReal f) x d < 0}) ∧
  Set.Nonempty (interior (tangentConeAt ℝ S x)):= by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 1.3.5 -/
lemma FCA_HUL_1_3_5 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x d : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_subdiff : Set.Nonempty (SubdifferentialI (liftEReal f) x)) :
  let S := sublevelSetFun (liftEReal f) x
  (IsNormalTo S x d) ↔
  (∃ (t : ℝ) (s : EuclideanSpace ℝ (Fin n)),
  (t ≥ 0) ∧ (s ∈ SubdifferentialI (liftEReal f) x) ∧ (d = t • s)) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 2.1.1 -/
lemma FCA_HUL_2_1_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let f'_ereal := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv (liftEReal f) x d
  let f'_real := fun (d : EuclideanSpace ℝ (Fin n)) => realDirectionalDeriv f x d
  (∀ x, f'_ereal x = f'_real x) ∧
  (∀ (ε : ℝ), (ε > 0) → ∃ δ > 0,
  ∀ (h : EuclideanSpace ℝ (Fin n)), ‖h‖ ≤ δ →
  abs (f (x + h) - f x - realDirectionalDeriv f x h) ≤ ε • ‖h‖) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 2.1.3 (i) -/
lemma FCA_HUL_2_1_3_i {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (s h : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) :
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  (h ∈ normalConeAt (SubdifferentialI (liftEReal f) x) s) →
  Asymptotics.IsLittleO (𝓝 0) (fun h => f (x + h) - f x - inner ℝ s h) (fun h => ‖h‖) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 2.1.3 (ii) -/
lemma FCA_HUL_2_1_3_ii {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (s h : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) :
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  (s ∈ exposedFace (SubdifferentialI (liftEReal f) x) h) →
  Asymptotics.IsLittleO (𝓝 0) (fun h => f (x + h) - f x - inner ℝ s h) (fun h => ‖h‖) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 2.1.5  -/
lemma FCA_HUL_2_1_5 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x d : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let f' := fun (d : EuclideanSpace ℝ (Fin n)) => directionalDeriv (liftEReal f) x d
  SubdifferentialI f' d = exposedFace (SubdifferentialI (liftEReal f) x) d := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 2.2.1  -/
lemma FCA_HUL_2_2_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) :
  List.TFAE [
    ∀ (y : EuclideanSpace ℝ (Fin n)), f y ≥ f x,
    0 ∈ SubdifferentialI (liftEReal f) x,
    ∀ (d : EuclideanSpace ℝ (Fin n)), directionalDeriv (liftEReal f) x d ≥ 0
  ] := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 2.3.1  -/
lemma FCA_HUL_2_3_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) (ht : 0 ≤ t ∧ t ≤ 1):
  let xt := t • y + (1 - t) • x
  let phi := fun (v : EuclideanSpace ℝ (Fin 1)) => f xt
  let t_asvec := fun _ => t
  -- work in ℝ, rather than EuclideanSpace ℝ (Fin n)
  let subdiff := {v : ℝ | ∃ v' ∈ SubdifferentialI (liftEReal phi) t_asvec, v' 0 = v}
  subdiff = {z : ℝ | ∃ s ∈ (SubdifferentialI (liftEReal f) xt), z = inner ℝ s (y - x)} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 2.3.3  -/
lemma FCA_HUL_2_3_3 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x y : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) (hxy : x ≠ y) :
  ∃ t ∈ Set.Ioo 0 1, ∃ s ∈ SubdifferentialI (liftEReal f) (t • y + (1 - t) • x),
  f y - f x = inner ℝ s (y - x) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 4.1.1  -/
lemma FCA_HUL_4_1_1 {n : ℕ}
  (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
  (t₁ t₂ : ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f₁ ∧ ConvexOn ℝ Set.univ f₂)
  (ht : t₁ > 0 ∧ t₂ > 0) :
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  SubdifferentialI (fun x => t₁ • (f₁ x) + t₂ • (f₂ x)) x =
  {v | ∃ v₁ ∈ (SubdifferentialI (liftEReal f₁) x), ∃ v₂ ∈ (SubdifferentialI (liftEReal f₂) x),
       v = t₁ • v₁ + t₂ • v₂} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 4.2.1  -/
lemma FCA_HUL_4_2_1 {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin m) → ℝ)
  (A₀ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
  (b : EuclideanSpace ℝ (Fin m))
  (hf_convex : ConvexOn ℝ Set.univ g) :
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  (SubdifferentialI (fun v => g (A₀ v + b)) x) = Set.image A₀.adjoint (SubdifferentialI (liftEReal g) (A₀ x + b)) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 4.3.1  -/
lemma FCA_HUL_4_3_1 {n m : ℕ}
  (f : ℕ → (EuclideanSpace ℝ (Fin n) → ℝ))
  (g : EuclideanSpace ℝ (Fin m) → ℝ)
  (hf_convex : ∀ i ∈ Finset.range m, ConvexOn ℝ Set.univ (f i))
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hg_increasing : ∀ y z, (∀ i, y i ≥ z i) → g y ≥ g z) :
  let F : (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m) :=
          fun x => (fun i => (f i) x)
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  SubdifferentialI (liftEReal (g ∘ F)) x =
  {v | ∃ ρ ∈ SubdifferentialI (liftEReal g) (F x), ∃ (s : ℕ → EuclideanSpace ℝ (Fin n)),
       (∀ i ∈ Finset.range m, s i ∈ SubdifferentialI (liftEReal (f i)) x) ∧
       (v = ∑ i : Fin m, (ρ i) • (s i))} := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 4.3.2  -/
lemma FCA_HUL_4_3_2 {n m : ℕ}
  (f : ℕ → (EuclideanSpace ℝ (Fin n) → ℝ))
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ∀ i ∈ Finset.range m, ConvexOn ℝ Set.univ (f i)) :
  let F : (EuclideanSpace ℝ (Fin n)) → ℝ := fun x => sSup (⋃ i ∈ Finset.range m, {(f i) x})
  let I := {i | (f i) x = F x}
  SubdifferentialI (liftEReal F) x = convexHull ℝ (⋃ i ∈ I, SubdifferentialI (liftEReal (f i)) x):= by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Lemma 4.4.1  -/
lemma FCA_HUL_4_4_1 {n : ℕ} {J : Type*}
  (f : J → (EuclideanSpace ℝ (Fin n) → ℝ))
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ∀ (i : J), ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ (j : J), (f j z : WithTop ℝ) < ⊤) :
  let F : (EuclideanSpace ℝ (Fin n)) → EReal := fun z => ⨆ (j : J), (f j z)
  let Jx := {j | f j x = F x}
  closure (convexHull ℝ (⋃ j ∈ Jx, SubdifferentialI (liftEReal (f j)) x)) ⊆
  SubdifferentialI F x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 4.4.2  -/
lemma FCA_HUL_4_4_2 {n : ℕ} {J : Type*} [TopologicalSpace J] [CompactSpace J]
  (f : J → (EuclideanSpace ℝ (Fin n) → ℝ))
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ∀ (i : J), ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ (j : J), (f j z : WithTop ℝ) < ⊤)
  (hf_usc : ∀ (j : J), ∀ z, lscAt (fun v => -1 • f j v) z) :
  let F : (EuclideanSpace ℝ (Fin n)) → EReal := fun z => ⨆ (j : J), (f j z)
  let Jx := {j | f j x = F x}
  convexHull ℝ (⋃ j ∈ Jx, SubdifferentialI (liftEReal (f j)) x) =
  SubdifferentialI F x := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 4.4.4  -/
lemma FCA_HUL_4_4_4 {n : ℕ} {J : Type*} [TopologicalSpace J] [CompactSpace J]
  (f : J → (EuclideanSpace ℝ (Fin n) → ℝ))
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ∀ (i : J), ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ (j : J), (f j z : WithTop ℝ) < ⊤)
  (hf_usc : ∀ (j : J), ∀ z, lscAt (fun v => -1 • f j v) z)
  (hf_differentiable : ∀ (j : J), Differentiable ℝ (f j)) :
  let F : (EuclideanSpace ℝ (Fin n)) → EReal := fun z => ⨆ (j : J), (f j z)
  let Jx := {j | f j x = F x}
  SubdifferentialI F x = convexHull ℝ (⋃ j ∈ Jx, {gradient (f j) x}) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 4.4.5  -/
lemma FCA_HUL_4_4_5 {n p : ℕ}
  (Y : Set (EuclideanSpace ℝ (Fin p)))
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p) → ℝ)
  (x₀ : EuclideanSpace ℝ (Fin n))
  (hf_usc : ∀ x, ∀ y, lscAt (fun v => -1 • (g x v)) y)
  (hf_convex : ∀ y ∈ Y, ConvexOn ℝ Set.univ (fun x => g x y))
  (hf_differentiable : ∀ y ∈ Y, Differentiable ℝ (fun x => g x y))
  (hf_finite : ∀ x, ⨆ y ∈ Y, (g x y : WithTop ℝ) < ⊤) :
  let F : EuclideanSpace ℝ (Fin n) → EReal := fun x => ⨆ y ∈ Y, (g x y : EReal)
  ∃ (F_finite : EuclideanSpace ℝ (Fin n) → ℝ),
  ∃! (y₀ : EuclideanSpace ℝ (Fin p)),
  (∀ x, F_finite x = F x) ∧
  (y₀ ∈ Y) ∧
  (IsMaxOn (fun y => g x₀ y) Y y₀) →
  (Differentiable ℝ F_finite) ∧
  (gradient F_finite x₀ = gradient (fun x => g x y₀) x₀) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 4.5.1  -/
lemma FCA_HUL_4_5_1 {m n : ℕ}
  (g : EuclideanSpace ℝ (Fin m) → ℝ)
  (A : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hA_surjective : Function.Surjective A) :
  let Ag := fun x => sInf (Set.image g {y | A y = x})
  let Yx := {y | (A y = x) ∧ (g y = Ag x)}
  (Set.Nonempty Yx) → ∀ y ∈ Yx,
  (SubdifferentialI (liftEReal Ag) x =
  {s | A.adjoint s ∈ SubdifferentialI (liftEReal g) y}) ∧
  (SubdifferentialI (liftEReal Ag) x =
  Set.preimage A.adjoint (SubdifferentialI (liftEReal g) y)) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 4.5.2  -/
lemma FCA_HUL_4_5_2 {m n : ℕ}
  (g : EuclideanSpace ℝ (Fin m) → ℝ)
  (A : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hA_surjective : Function.Surjective A) :
  let Ag := fun x => sInf (Set.image g {y | A y = x})
  let Yx := {y | (A y = x) ∧ (g y = Ag x)}
  (Set.Nonempty Yx) → (∃ y ∈ Yx, DifferentiableAt ℝ g y) →
  (DifferentiableAt ℝ Ag x) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 4.5.5  -/
lemma FCA_HUL_4_5_5 {n : ℕ}
  (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ)
  (y₁ y₂ : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f₁ ∧ ConvexOn ℝ Set.univ f₂)
  (hf_minorized : ∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ),
                 ∀ x, (inner ℝ s x + b ≤ f₁ x) ∧ (inner ℝ s x + b ≤ f₂ x)) :
  let infconv := infimalConv f₁ f₂
  (infconv (y₁ + y₂) = f₁ y₁ + f₂ y₂) →
  SubdifferentialI infconv (y₁ + y₂) =
  (SubdifferentialI (liftEReal f₁) y₁) ∩ (SubdifferentialI (liftEReal f₂) y₂) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 6.1.1  -/
lemma FCA_HUL_6_1_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x₁ x₂ : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) :
  ∀ s₁ ∈ SubdifferentialI (liftEReal f) x₁, ∀ s₂ ∈ SubdifferentialI (liftEReal f) x₂,
  inner ℝ (s₂ - s₁) (x₂ - x₂) ≥ 0 := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 6.1.2  -/
lemma FCA_HUL_6_1_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (c : ℝ)
  (hC_convex : Convex ℝ C) (hc : c > 0) :
  StrongConvexOn C c f ↔
  ∀ x₁ ∈ C, ∀ x₂ ∈ C, ∀ s ∈ SubdifferentialI (liftEReal f) x₁,
  f x₂ ≥ f x₁ + inner ℝ s (x₂ - x₁) + (c / 2) * ‖x₂ - x₁‖^2 := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 6.1.3  -/
lemma FCA_HUL_6_1_3 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_convex : Convex ℝ C) :
  StrictConvexOn ℝ C f ↔
  ∀ x₁ ∈ C, ∀ x₂ ∈ C, (x₁ ≠ x₂) →
  ∀ s ∈ SubdifferentialI (liftEReal f) x₁,
  f x₂ > f x₁ + inner ℝ s (x₂ - x₁) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 6.2.1  -/
lemma FCA_HUL_6_2_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let graph_subdiff := ⋃ x, {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
                                  z.1 = x ∧ z.2 ∈ SubdifferentialI (liftEReal f) x}
  IsClosed graph_subdiff := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Proposition 6.2.2  -/
lemma FCA_HUL_6_2_2 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let subdiff_im := fun (C : Set (EuclideanSpace ℝ (Fin n))) =>
                     {v | ∃ x, v ∈ SubdifferentialI (liftEReal f) x}
  ∀ (B : Set (EuclideanSpace ℝ (Fin n))),
  Bornology.IsBounded B → Bornology.IsBounded (subdiff_im B) := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 6.2.4  -/
lemma FCA_HUL_6_2_4 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let subdiff_neighborhood := fun (ε : ℝ) =>
                              {v | ∃ w d,(‖d‖ ≤ ε) ∧ (w ∈ SubdifferentialI (liftEReal f) x) ∧ (v = w + d)}
  ∀ ε > 0, ∃ δ > 0, ∀ y,
  y ∈ Metric.ball x δ → SubdifferentialI (liftEReal f) y ⊆ subdiff_neighborhood ε := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 6.2.5  -/
lemma FCA_HUL_6_2_5 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  ∀ (d : EuclideanSpace ℝ (Fin n)),
  directionalDeriv (liftEReal f) x d =
  Filter.limsup (fun y => directionalDeriv (liftEReal f) y d) (𝓝 x):= by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Theorem 6.2.7  -/
lemma FCA_HUL_6_2_7 {n : ℕ}
  (fk : ℕ → (EuclideanSpace ℝ (Fin n) → ℝ))
  (xk : ℕ → EuclideanSpace ℝ (Fin n))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (fk i))
  (hf_pointwise : ∀ v, Filter.Tendsto (fun k => fk k v) Filter.atTop (𝓝 (f v)))
  (hx_limit : Filter.Tendsto xk Filter.atTop (𝓝 x)) :
  let subdiff_neighborhood := fun (ε : ℝ) =>
                              {v | ∃ w d,(‖d‖ ≤ ε) ∧ (w ∈ SubdifferentialI (liftEReal f) x) ∧ (v = w + d)}
  ∀ ε > 0, ∃ (K : ℕ), ∀ k ≥ K,
  SubdifferentialI (liftEReal (fk k)) (xk k) ⊆ subdiff_neighborhood ε:= by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 6.2.8  -/
lemma FCA_HUL_6_2_8 {n : ℕ}
  (fk : ℕ → (EuclideanSpace ℝ (Fin n) → ℝ))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (fk i))
  (hf_seq_diff : ∀ i, Differentiable ℝ (fk i))
  (hf_diff : Differentiable ℝ f)
  (hf_pointwise : ∀ v, Filter.Tendsto (fun k => fk k v) Filter.atTop (𝓝 (f v))) :
  ∀ (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K →
  TendstoUniformlyOn (fun k => (fun x => gradient (fk k) x)) (fun x => gradient f x) Filter.atTop K := by
  sorry

/- Hiriart-Urruty Lemarechal (Fundamentals of Convex analysis), Section D, Corollary 6.3.1  -/
lemma FCA_HUL_6_3_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let delta_set := {y | SubdifferentialI (liftEReal f) y = {gradient f y}}
  let lim_set := fun x => {s | ∃ (yk : ℕ → EuclideanSpace ℝ (Fin n)),
                               (∀ k, yk k ∈ delta_set) ∧
                               (Filter.Tendsto yk Filter.atTop (𝓝 x)) ∧
                               (Filter.Tendsto (fun k => gradient f (yk k)) Filter.atTop (𝓝 s))}
  ∀ (x : EuclideanSpace ℝ (Fin n)),
  SubdifferentialI (liftEReal f) x = convexHull ℝ (lim_set x) := by
  sorry
