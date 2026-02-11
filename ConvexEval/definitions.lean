import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-
  General set operations
-/

/- Add two sets  -/
def set_add {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (K : Set (EuclideanSpace ℝ (Fin n)))
    : Set (EuclideanSpace ℝ (Fin n))
    := {v : EuclideanSpace ℝ (Fin n) | ∃ c ∈ C, ∃ k ∈ K, v = c + k}

/- Translate a set -/
def translate_set {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
  : Set (EuclideanSpace ℝ (Fin n))
  := {v : EuclideanSpace ℝ (Fin n) | ∃ c ∈ C, v = (c - x)}

/-
  Convex sets
-/

/- Unit Simplex -/
def Δκ (k : ℕ) : Set (EuclideanSpace ℝ (Fin k))
    := {v : (EuclideanSpace ℝ (Fin k)) | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

def conv {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
    := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → (EuclideanSpace ℝ (Fin n))) (_ : ∀ i, x i ∈ S),
         {v : (EuclideanSpace ℝ (Fin n)) |
          ∃ (a : (EuclideanSpace ℝ (Fin k))),
          (a ∈ (Δκ k)) ∧ (v = ∑ i, a i • x i)}

/- Conical hull -/
def cone {m n : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin n))
    : Set (EuclideanSpace ℝ (Fin n))
    := {v : EuclideanSpace ℝ (Fin n) |
        ∃ (α : EuclideanSpace ℝ (Fin m)) (_ : ∀ i, α i ≥ 0), v = ∑ i, α i • x i}

/- Affine hull -/
def affineHull {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
  := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → (EuclideanSpace ℝ (Fin n))) (_ : ∀ i, x i ∈ C),
     {v : (EuclideanSpace ℝ (Fin n)) |
      ∃ (a : (EuclideanSpace ℝ (Fin k))), (∑ i, a i = 1) ∧ (v = ∑ i, a i • x i)}

/- Asymptotic (recession) cone, defined for closed convex sets C -/
def AsymptoticCone {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ∀ t, t > 0 → x + t • d ∈ C}

/- Face -/
def Face {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (F : Set (EuclideanSpace ℝ (Fin n))) : Prop
    := (F ⊆ C) ∧ (Set.Nonempty F) ∧ (Convex ℝ F) ∧
       ∀ (x₁ x₂ : EuclideanSpace ℝ (Fin n)) (_ : x₁ ∈ C ∧ x₂ ∈ C)
       (α : ℝ) (_ : α > 0 ∧ α < 1) (_ : α • x₁ + (1 - α) • x₂ ∈ F),
       {v : EuclideanSpace ℝ (Fin n) | ∃ θ, (θ ≥ 0) ∧ (θ ≤ 1) ∧ (v = θ • x₁ + (1-θ) • x₂)} ⊆ F

/- Hyperplane -/
def Hyperplane {n : ℕ}
  (s : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | inner ℝ s x ≤ t}

/- Indexing set of hyperplanes -/
def I_C {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n) × ℝ)
    := {(s, r) : EuclideanSpace ℝ (Fin n) × ℝ | C ⊆ Hyperplane s r}

/- Supporting hyperplane at point -/
def SupportingHyperplaneAt {n : ℕ} (s x : EuclideanSpace ℝ (Fin n)) (r : ℝ)
  (C : Set (EuclideanSpace ℝ (Fin n))) : Prop
  := (s ≠ 0) ∧ (x ∈ C) ∧ (C ⊆ Hyperplane s r) ∧ (x ∈ Hyperplane s r) ∧ (inner ℝ s x = r)

/- Supporting hyperplane -/
def IsSupportingHyperplane {n : ℕ}
  (s : EuclideanSpace ℝ (Fin n)) (t : ℝ)
  (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ y ∈ C, inner ℝ s y ≤ t

/- ExposedFace -/
def IsExposedFace {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) (F : Set (EuclideanSpace ℝ (Fin n))) : Prop
  := (F ⊆ C) ∧
     ∃ (s : EuclideanSpace ℝ (Fin n)) (r : ℝ), (∀ y ∈ C, inner ℝ s y ≤ r) ∧
     (F = C ∩ Hyperplane s r) ∧ (s ≠ 0)

/- Exposed face -/
def exposedFace {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (s : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x : EuclideanSpace ℝ (Fin n) | inner ℝ s x = sSup (Set.image (fun y => inner ℝ s y) C)}

/- Convex cone criteria -/
def IsConvexCone {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop
    := ∀ x ∈ C, ∀ y ∈ C, ∀ (α : ℝ) (_ : α ≥ 0), ∀ (β : ℝ) (_ : β ≥ 0), α • x + β • y ∈ C

/- Normal -/
def IsNormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s : E) (C : Set E)
  (x : E) : Prop :=
  ∀ y ∈ C, inner ℝ s (y - x) ≤ 0

/- Tangent -/
def IsTangent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (d : E) (S : Set E)
  (x : E)
  : Prop
  := ∃ (s : ℕ → E) (t : ℕ → ℝ),
     (∀ i, s i ∈ S) ∧ (Filter.Tendsto s Filter.atTop (𝓝 x)) ∧
     (∀ i, t i > 0) ∧ (Filter.Tendsto t Filter.atTop (𝓝[>] 0)) ∧
     (Filter.Tendsto (fun i => (t i)⁻¹ • (s i - x)) Filter.atTop (𝓝 d))

/- Polar cone -/
def PolarCone {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {s : EuclideanSpace ℝ (Fin n) | ∀ x ∈ K, inner ℝ s x ≤ 0}

/- Normal cone -/
def NormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : E) (C : Set E) : Set E :=
  {s : E | IsNormal s C x}

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

/- Tangent cone -/
def TangentCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (S : Set E) : Set E
    := {d : E | IsTangent d S x}

/- Cone of set -/
def GenCone {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
  : Set (EuclideanSpace ℝ (Fin n))
  := {v : EuclideanSpace ℝ (Fin n) |
      ∃ (α : ℝ) (_ : α ≥ 0),
      ∃ (x : EuclideanSpace ℝ (Fin n)) (_ : x ∈ S),
      v = α • x}

/- Is cone -/
def IsCone {E : Type*} [AddCommMonoid E] [SMul ℝ E]
  (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ (s : ℝ), s > 0 → s • x ∈ K

/-
  Proven properties of convex sets
-/

/- Polar cone is convex -/
lemma polarCone_isConvex {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    : Convex ℝ (PolarCone K) := by
    intro x hx y hy a b ha hb hab
    have h_combo : ∀ z ∈ K, inner ℝ (a • x + b • y) z ≤ 0 := by
        intro z hz
        simp [inner_add_left, inner_smul_left_eq_star_smul]
        have hx' : a * (inner ℝ x z) ≤ 0 := by
            have non_mul_x := hx.out z hz
            have := mul_le_mul_of_nonneg_left non_mul_x ha
            simpa [mul_zero] using this
        have hy' : b * (inner ℝ y z) ≤ 0 := by
            have non_mul_y := hy.out z hz
            have := mul_le_mul_of_nonneg_left non_mul_y hb
            simpa [mul_zero] using this
        have := add_le_add hx' hy'
        simpa [add_zero] using this
    exact h_combo

/- Polar cone is closed -/
lemma polarCone_isClosed {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    : IsClosed (PolarCone K) := by
    have pc_intersection : (PolarCone K) = ⋂ x ∈ K,
        {s : EuclideanSpace ℝ (Fin n) | inner ℝ s x ≤ 0} := by
        ext s
        simp [PolarCone]
    rw [pc_intersection]
    have h_cont (x : EuclideanSpace ℝ (Fin n)) : Continuous (fun s => inner ℝ s x) :=
        continuous_inner.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ => x)))
    have h_closed : ∀ x ∈ K, IsClosed {s : EuclideanSpace ℝ (Fin n) | inner ℝ s x ≤ 0} := by
        intro x _
        exact IsClosed.preimage (h_cont x) isClosed_Iic
    exact isClosed_biInter h_closed

/- Polar cone is nonempty -/
lemma polarCone_isNonempty {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    : Set.Nonempty (PolarCone K) := ⟨0, by simp [PolarCone]⟩

/- Convex cone is convex -/
lemma convexCone_isConvex {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsConvexCone C)
    : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    exact hC x hx y hy a ha b hb

/-
  Operations on convex sets
-/

/- Projection -/
noncomputable def pC {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C)
    : EuclideanSpace ℝ (Fin n)
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

/- Support function -/
noncomputable def SupportFun {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ :=
  sSup (Set.image (fun v => inner ℝ v x) S)

/- Direction exposing face
  * note that d ≠ 0
-/
def DirectionExposingFace {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (d : EuclideanSpace ℝ (Fin n))
  : Set (EuclideanSpace ℝ (Fin n)) :=
  let σ := SupportFun C
  {x | (x ∈ C) ∧ (inner ℝ x d = σ d)}


/-
  Other definitions
-/

/- Argmax -/
def Argmax {n : ℕ} (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (C : Set (EuclideanSpace ℝ (Fin n)))
  : Set (EuclideanSpace ℝ (Fin n))
  := {x : EuclideanSpace ℝ (Fin n) | (x ∈ C) ∧ (∀ y ∈ C, f y ≤ f x)}

/-
  General function conventions
-/

/- Standard convention where 0*(+∞) = 0
   The definition of ConvexOn involves uses SMul for both sides of the defining inequality.
 -/
noncomputable instance : SMul ℝ (WithTop ℝ) where
  smul t x := match x with
    | ⊤ => if t = 0 then 0 else ⊤
    | some r => some (t * r)

/- Standard convention where 0*(±∞) = 0
 -/
noncomputable instance : SMul ℝ EReal where
  smul t x := match x with
    | ⊤ => if t = 0 then 0 else ⊤
    | ⊥ => if t = 0 then 0 else ⊥
    | some r => some (t * r)

/-
  Other function helpers
-/

/- View a `WithTop ℝ`-valued function as a `EReal`-valued one. -/
def liftWithToptoEReal {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
  EuclideanSpace ℝ (Fin n) → EReal
  := fun x => (f x : WithBot (WithTop ℝ))

/- View a `ℝ`-valued function as a `WithTop ℝ`-valued one. -/
def liftRealtoWT {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) :
  EuclideanSpace ℝ (Fin n) → WithTop ℝ
  := fun x => (f x : WithTop ℝ)

/- View a `ℝ`-valued function as a `EReal`-valued one. -/
def liftRealtoEReal {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) :
  EuclideanSpace ℝ (Fin n) → EReal
  := fun x => (f x : EReal)

/- Distance -/
noncomputable def DistOnFunctions {n : ℕ}
  (σ₁ : EuclideanSpace ℝ (Fin n) → ℝ)
  (σ₂ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  sSup (Set.image
       (fun x => AbsoluteValue.abs (σ₁ x - σ₂ x))
       {x | ‖x‖ ≤ 1})

/- Scalar product -/
def IsScalarProduct {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ (u v : EuclideanSpace ℝ (Fin n)), f u v = f v u) ∧
  (∀ (u v : EuclideanSpace ℝ (Fin n)) (a : ℝ), f (a • u) v = a • (f v u)) ∧
  (∀ (u v w : EuclideanSpace ℝ (Fin n)), f (u + w) v = f v u + f w v) ∧
  (∀ (u : EuclideanSpace ℝ (Fin n)), f u u ≥ 0)

/- Helper for getting the first n-coordinates -/
def vecHead {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n)
  := fun i => x (Fin.castSucc i)

/- Helper for getting the last coordinate -/
def vecLast {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ
  := x (Fin.last n)

/-
  Convex functions
-/

def effDom {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n))
  := {x : EuclideanSpace ℝ (Fin n) | f x < ⊤ ∧ f x > ⊥}

/- Epigraph of a function -/
def epigraph {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n) × ℝ)
  := {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ p.2}

def strictEpigraph {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Set (EuclideanSpace ℝ (Fin n) × ℝ)
  := {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 < p.2}

/- Lower semi-continuous at -/
noncomputable def lscAt {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop
  := Filter.liminf f (𝓝 x) ≥ f x

noncomputable def lscHull {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := Filter.liminf f (𝓝 x)

def InConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x < ⊤) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y))

def InProperConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop
  := (∃ x, f x < ⊤) ∧ (∀ x, f x ≠ ⊥) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y))

def InClosedConvRn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x < ⊤) ∧
     (∀ x, ∀ y, ∀ (α : ℝ), (0 ≤ α) → (α ≤ 1) → f (α • x + (1 - α) • y) ≤ α • (f x) + (1 - α) • (f y)) ∧
     (∀ x, (lscHull f) x = f x)

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

def Minorizes {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (g : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  : Prop
  := ∀ x, f x ≤ g x

/-
  Specific functions
-/
noncomputable def perspective {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (u : ℝ) (x : EuclideanSpace ℝ (Fin n))
  : WithTop ℝ :=
  if u > 0 then
    u * f (u⁻¹ • x)
  else
    ⊤

noncomputable def imageFun {m n : ℕ}
  (A : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)))
  (g : EuclideanSpace ℝ (Fin m) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : EReal
  := sInf (Set.image g {y : EuclideanSpace ℝ (Fin m) | A y = x})

noncomputable def valueFun {p n : ℕ}
  (phi : EuclideanSpace ℝ (Fin p) → EReal)
  (c : (Fin n) → (EuclideanSpace ℝ (Fin p) → EReal))
  (x : EuclideanSpace ℝ (Fin n)) : EReal
  := sInf (Set.image phi {u | ∀ j, (c j) u ≤ x j})

noncomputable def marginalFun {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin (n + m)) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : EReal
  := let g_concat : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EReal := fun a b
                     => g (Fin.append (α := ℝ) a b)
     sInf (Set.range (g_concat x))

/- Asymptotic (recession) function -/
noncomputable def AsymptoticFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x₀ d : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := limUnder Filter.atTop (fun (t : ℝ) => t⁻¹ • (f (x₀ + t • d) - f x₀))

/- Indicator function -/
noncomputable def Indicator {n : ℕ}
  (H : Subspace ℝ (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  : WithTop ℝ := by
    classical
    exact if x ∈ H then 0 else ⊤

/- Image function -/
noncomputable def ImageFunction {m n : ℕ}
  (A : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  (g : EuclideanSpace ℝ (Fin m) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : WithTop ℝ :=
  let A_inv := {y : EuclideanSpace ℝ (Fin m) | A y = x}
  sInf (Set.image g A_inv)

/- Infimal convolution -/
noncomputable def infimalConv {n : ℕ}
  (f₁ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (f₂ : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : EReal
  := sInf { z : WithBot (WithTop ℝ) | ∃ y : EuclideanSpace ℝ (Fin n),
                                      z = ((f₁ y + f₂ (x - y) : WithTop ℝ) : WithBot (WithTop ℝ)) }

/- Infimal convolution -/
noncomputable def multiInfimalConv {n : ℕ} (m : ℕ)
  (f : ℕ → (EuclideanSpace ℝ (Fin n) → WithTop ℝ))
  (x : EuclideanSpace ℝ (Fin n)) : WithBot (WithTop ℝ)
  := sInf {z : WithBot (WithTop ℝ) |
           ∃ (y : ℕ → EuclideanSpace ℝ (Fin n)),
           x = ∑ i ∈ Finset.range m, (y i) ∧
           z = ∑ i ∈ Finset.range m, (f i) (y i)}

/- Sublevel set -/
def sublevelSetFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y : EuclideanSpace ℝ (Fin n) | f y ≤ f x}

/- Image of a linear operator -/
def Im {m n : ℕ}
  (A : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
  := {z | ∃ y, A y = z}

/-
  Properties of functions
-/

/- Nondegeneracy conditions for functions -/
def IsNondegenerate {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∃ x, f x ≠ ⊤) ∧ (∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

/- Is subadditive -/
def IsSubadditive {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop :=
  ∀ (x₁ : EuclideanSpace ℝ (Fin n)), ∀ (x₂ : EuclideanSpace ℝ (Fin n)),
  f (x₁ + x₂) ≤ (f x₁) + (f x₂)

/- Is a closed function -/
def IsClosedFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := (∀ x, (lscHull f) x = f x)

/- Positively homogeneous with degree k -/
def IsKPosHomogeneous {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (k : ℝ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin n)), ∀ (t : ℝ),
  t > 0 → f (t • x) = (t ^ k) • (f x)

/- Linear function -/
def IsLinearOn {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (σ : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop :=
  (InConvRn σ) ∧
  (∀ (x₁ x₂ : EuclideanSpace ℝ (Fin n)), ∀ (t₁ t₂ : ℝ),
  x₁ ∈ 𝓧 → x₂ ∈ 𝓧 → σ (t₁ • x₁ + t₂ • x₂) = t₁ • (σ x₁) + t₂ • (σ x₂))

/- In the subspace spanned by m vectors -/
def InSubspaceSpanVec {n : ℕ} (m : ℕ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (x' : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (z : ℕ → EuclideanSpace ℝ (Fin n)),
  ∃ (s : ℕ → ℝ),
  (∀ i ∈ Finset.range m, ∃ j ∈ Finset.range m, z i = x j) ∧
  (x' = ∑ i ∈ Finset.range m, (s i) • (z i))

/- Is minorized on set -/
def IsMinorizedOn {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (s : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x ∈ C, f x ≥ inner ℝ s x - b

/- Sublinear function -/
def IsSublinear {n : ℕ}
  (σ : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  (∀ (x₁ x₂ : EuclideanSpace ℝ (Fin n)), ∀ (t₁ t₂ : ℝ),
  t₁ > 0 → t₂ > 0 → σ (t₁ • x₁ + t₂ • x₂) ≤ t₁ • (σ x₁) + t₂ • (σ x₂))

/-
  Subgradients
-/

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
  (directionalDeriv (liftRealtoEReal f) x d).toReal

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

/- Value finite -/
def IsFinite (z : EReal) : Prop :=
  ∃ r : ℝ, z = (r : EReal)

/- Conjugate of a function (Legendre-Fenchel transform) -/
noncomputable def Conjugate {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
  (s : EuclideanSpace ℝ (Fin n)) : WithTop ℝ
  := sSup {z : WithTop ℝ | ∃ x ∈ effDom (liftWithToptoEReal f), z = inner ℝ s x - f x}

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

/- 0-coercive function -/
noncomputable def IsZeroCoerciveFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := Filter.Tendsto f (Filter.comap norm Filter.atTop) Filter.atTop

/- 1-coercive function -/
noncomputable def IsOneCoerciveFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop
  := Filter.Tendsto (fun x => (norm x)⁻¹ • f x) (Filter.comap norm Filter.atTop) Filter.atTop
