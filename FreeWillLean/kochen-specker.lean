import FreeWillLean.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib
/-
Need to define the space of 3D directions, and need to define 101 function
then need to prove some basic lemmas about this function
-/


namespace FreeWillLean

inductive SpinMeasurement : Type
| zero
| one

open SpinMeasurement

instance : DecidableEq SpinMeasurement :=
  fun x y => match x, y with
    | zero, zero => isTrue rfl
    | one, one => isTrue rfl
    | zero, one => isFalse (by simp)
    | one, zero => isFalse (by simp)

@[simp]
def SquaredNorm (v : Fin 3 → ℝ) : ℝ :=
  Matrix.dotProduct v v

def MeasurementDirection : Type :=
  {v : Fin 3 → ℝ // SquaredNorm v = 1}

@[simp]
def MeasurementDirection.index (d : MeasurementDirection) (i : Fin 3) : ℝ :=
  d.val i

notation d "[" i "]" => MeasurementDirection.index d i

noncomputable def v1 : MeasurementDirection := ⟨![1/√3, 1/√3, 1/√3], by
  simp ; ring_nf ; simp⟩

def v2 : MeasurementDirection := ⟨!₂[1, 0, 0], by
  simp⟩

def IsPerpendicular (d1 d2 : MeasurementDirection) : Prop :=
  Matrix.dotProduct d1.val d2.val = 0

def IsMutuallyPerpendicular(d1 d2 d3 : MeasurementDirection) : Prop :=
  IsPerpendicular d1 d2 ∧ IsPerpendicular d2 d3∧ IsPerpendicular d1 d3

def ValidThriples : List (List SpinMeasurement) :=
  [[zero, one, one], [one, zero, one], [one, one, zero]]

def IsOneZeroOneFunc (f : MeasurementDirection → SpinMeasurement) : Prop :=
  ∀ d1 d2 d3 : MeasurementDirection, IsMutuallyPerpendicular d1 d2 d3 → [f d1, f d2, f d3] ∈ ValidThriples

def OneZeroOneFunc : Type :=
  {f : (MeasurementDirection → SpinMeasurement) // IsOneZeroOneFunc f}

def apply (f : OneZeroOneFunc) (a : MeasurementDirection) : SpinMeasurement :=
  f.val a


set_option pp.analyze true

theorem norm_def (v : MeasurementDirection) :
  v[0] ^ 2 + v[1] ^ 2 + v[2] ^ 2 = 1 :=
by
  have hnorm : Matrix.dotProduct v.1 v.1 = 1 := by apply v.2
  rw [Matrix.dotProduct] at hnorm
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at hnorm
  simp at hnorm
  rw [MeasurementDirection.index, MeasurementDirection.index, MeasurementDirection.index]
  calc
    v.val 0 ^ 2 + v.val 1 ^ 2 + v.val 2 ^ 2 = v.val 0 * v.val 0 + (v.val 1 * v.val 1 + v.val 2 * v.val 2) := by ring
    _ = 1 := by exact hnorm

def CompleteBasis (d1 d2 : MeasurementDirection) (hperp : IsPerpendicular d1 d2): MeasurementDirection :=
  ⟨!₂[d1[1] * d2[2] - d1[2] * d2[1], d1[2] * d2[0] - d1[0] * d2[2], d1[0] * d2[1] - d1[1] * d2[0]], by
    simp
    rw [IsPerpendicular, Matrix.dotProduct] at hperp
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at *; simp at * ; ring_nf at *

    let a := d1[0]
    let b := d1[1]
    let c := d1[2]
    let x := d2[0]
    let y := d2[1]
    let z := d2[2]

    have hnd1 : a^2 + b^2 + c^2 = 1 := norm_def d1
    have hnd2 : x^2 + y^2 + z^2 = 1 := norm_def d2
    have h0 : d1[1] * d2[1] + d2[2] * d1[2] + d2[0] * d1[0] = 0 := by simp [MeasurementDirection.index] ; exact hperp

    have hab : a^2 + b^2 = 1 - c^2 := by rw [←hnd1] ; ring
    have hbc : b^2 + c^2 = 1 - a^2 := by rw [←hnd1] ; ring
    have hca : c^2 + a^2 = 1 - b^2 := by rw [←hnd1] ; ring
    calc
      (-(b * z * c * y * 2) - b * y * x * a * 2 + b ^ 2 * z ^ 2 +
      (b ^ 2 * x ^ 2 - z * c * x * a * 2) + z ^ 2 * a ^ 2 + c ^ 2 * y ^ 2 +
      c ^ 2 * x ^ 2 + y ^ 2 * a ^ 2) =
      (x ^ 2 * (b ^ 2 + c ^ 2) + y ^ 2 * (c ^ 2 + a ^ 2) + z ^ 2 * (a ^ 2 + b ^ 2)
      - (2 * b * z * c * y + 2 * b * y * x * a + 2 * z * c * x * a)) := by ring_nf
      _ = (x ^ 2 * (1 - a ^ 2) + y ^ 2 * (1 - b ^ 2) + z ^ 2 * (1 - c ^ 2)
      - (2 * b * z * c * y + 2 * b * y * x * a + 2 * z * c * x * a)) := by rw [hab, hbc, hca]
      _ = (x ^ 2 + y ^ 2 + z ^ 2 - (b * y + z * c + x * a) ^ 2) := by ring_nf
      _ = 1 := by rw [hnd2, h0] ; simp⟩



theorem valid_measurements_starting_zero (x y : SpinMeasurement) :
  [zero, x, y] ∈ ValidThriples → x = one :=
by
  intro hmem
  cases hmem with
  | head _ => rfl
  | tail _ hmem =>
    cases hmem with | tail _ hmem =>
    cases hmem with | tail _ hmem =>
    cases hmem

theorem perp_zero_implies_one (f : OneZeroOneFunc) (d1 d2 : MeasurementDirection) :
  apply f d1 = zero → IsPerpendicular d1 d2 → apply f d2 = one :=
by
  intro hd1z hperp12
  have hperp13 : IsPerpendicular d1 (CompleteBasis d1 d2 hperp12) := by
    rw [IsPerpendicular, CompleteBasis, Matrix.dotProduct] ; simp [MeasurementDirection.index]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]; simp ; ring
  have hperp23 : IsPerpendicular d2 (CompleteBasis d1 d2 hperp12) := by
    rw [IsPerpendicular, CompleteBasis, Matrix.dotProduct] ; simp [MeasurementDirection.index]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]; simp ; ring
  have hmutualperp : IsMutuallyPerpendicular d1 d2 (CompleteBasis d1 d2 hperp12) := by
    rw [IsMutuallyPerpendicular]
    apply And.intro hperp12 (And.intro hperp23 hperp13)
  have hvalidthrip : [apply f d1, apply f d2, apply f (CompleteBasis d1 d2 hperp12)] ∈ ValidThriples :=
    f.2 d1 d2 (CompleteBasis d1 d2 hperp12) hmutualperp
  rw [hd1z] at hvalidthrip
  apply valid_measurements_starting_zero
  exact hvalidthrip

theorem perp_one_one_implies_zero (f : OneZeroOneFunc) ( d1 d2 d3 : MeasurementDirection) :
  apply f d1 = one ∧ apply f d2 = one → IsMutuallyPerpendicular d1 d2 d3 → apply f d3 = zero :=
by
  intro hone hperp
  have hin : [apply f d1, apply f d2, apply f d3] ∈ ValidThriples := f.property d1 d2 d3 hperp
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq =>
    rw [hone.left] at heq
    have hnonsense : one = zero := heq.left
    contradiction
  | inr heq => cases heq with
    | inl heq =>
      rw [hone.right] at heq
      have hnonsense : one = zero := heq.right.left
      contradiction
    | inr heq =>
      exact heq.right.right

structure O3 where
  matrix : Matrix (Fin 3) (Fin 3) ℝ
  is_orth : matrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ

instance : Coe O3 (Matrix (Fin 3) (Fin 3) ℝ) :=
 {coe := fun m => m.matrix}


open scoped Matrix

theorem O3.dot_product_preservation (v1 v2 : Fin 3 → ℝ) (m : O3) :
  (m.matrix *ᵥ v1) ⬝ᵥ (m *ᵥ v2) = v1 ⬝ᵥ v2 :=
by
  have horth : mᵀ * m.matrix = 1 := by apply (Iff.mp (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ)) m.is_orth
  calc
    m *ᵥ v1 ⬝ᵥ m *ᵥ v2  = (m *ᵥ v1) ᵥ* m ⬝ᵥ v2 := by exact Matrix.dotProduct_mulVec (m *ᵥ v1) m.matrix v2
    _ = v1 ᵥ* (mᵀ * m.matrix) ⬝ᵥ v2 := by rw [Matrix.vecMul_mulVec]
    _ = v1 ⬝ᵥ v2 := by simp [horth]

theorem O3.norm_preservation (v : Fin 3 → ℝ) (m : O3) :
  SquaredNorm (m *ᵥ v) = SquaredNorm v :=
by
  rw [SquaredNorm, SquaredNorm]
  exact O3.dot_product_preservation v v m

def O3.function (o : O3) : MeasurementDirection → MeasurementDirection :=
  fun d => ⟨o *ᵥ d.val, by rw [O3.norm_preservation] ; exact d.2⟩

theorem O3.OneZeroOneFunc_invariance (f : MeasurementDirection → SpinMeasurement)  (m : O3) :
  IsOneZeroOneFunc f → IsOneZeroOneFunc (f ∘ m.function) :=
by
  intro hf
  rw [IsOneZeroOneFunc] at *
  intro d1 d2 d3 hperp
  repeat rw [Function.comp] ; repeat rw [O3.function]
  apply hf ; rw [IsMutuallyPerpendicular] at * ; repeat (rw [IsPerpendicular] at *)
  apply And.intro
  { rw [O3.dot_product_preservation] ; exact hperp.left}
  { apply And.intro
    {rw [O3.dot_product_preservation] ; exact hperp.right.left}
    {rw [O3.dot_product_preservation] ; exact hperp.right.right}
  }

def O3.compose_OneZeroOneFunc (f : OneZeroOneFunc) (m : O3) : OneZeroOneFunc :=
  ⟨f.val ∘ m.function, by exact O3.OneZeroOneFunc_invariance f.val m f.property⟩

syntax "vec_norm" : tactic

macro_rules
  | `(tactic| vec_norm) => `(tactic| first
    | (simp ;ring_nf ; simp ; norm_num)
    | (simp ; ring_nf ; simp)
    | simp)

syntax "prove_orth" : tactic
macro_rules
  | `(tactic| prove_orth) => `(tactic|
      (apply (Iff.mpr (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ))
       rw [star, Matrix.instStar]; simp
       ext i j
       simp [Matrix.mul_apply]
       fin_cases i <;> fin_cases j
       all_goals { simp; first | (exact rfl) | exact Eq.symm (neg_eq_iff_eq_neg.mp rfl)}))




noncomputable def x : MeasurementDirection := ⟨![1, 0, 0], by vec_norm⟩
noncomputable def y : MeasurementDirection := ⟨![0, 1, 0], by vec_norm⟩
noncomputable def z : MeasurementDirection := ⟨![0, 0, 1], by vec_norm⟩
noncomputable def a1 : MeasurementDirection := ⟨![0, 1 / √2, 1 / √2], by vec_norm⟩
noncomputable def a2 : MeasurementDirection := ⟨![0, -1 / √2, 1 / √2], by vec_norm⟩
noncomputable def a3 : MeasurementDirection := ⟨![0, -1 / √2, -1 / √2], by vec_norm⟩
noncomputable def b1 : MeasurementDirection := ⟨![1 / √2, 1 / 2, 1 / 2], by vec_norm⟩
noncomputable def b2 : MeasurementDirection := ⟨![1 / √2, -1 / 2, -1 / 2], by vec_norm⟩
noncomputable def b3 : MeasurementDirection := ⟨![1 / √2, -1 / 2, 1 / 2], by vec_norm⟩
noncomputable def b4 : MeasurementDirection := ⟨![1 / √2, 1 / 2, -1 / 2], by vec_norm⟩

theorem perp_xyz : IsMutuallyPerpendicular x y z :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [x, y])
  apply And.intro (by simp [y, z]) (by simp [x, z])

theorem perp_a2b1b2 : IsMutuallyPerpendicular a2 b1 b2 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [a2, b1] ; ring_nf)
  apply And.intro (by simp [b1, b2] ; ring_nf ; norm_num) (by simp [a2, b2] ; ring_nf)

theorem perp_a1b3b4 : IsMutuallyPerpendicular a1 b3 b4 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [a1, b3] ; ring_nf)
  apply And.intro (by simp [b3, b4] ; ring_nf ; norm_num) (by simp [a1, b4] ; ring_nf)

theorem perp_xa1 : IsPerpendicular x a1 :=
by
  rw [IsPerpendicular]
  simp [x, a1]

theorem perp_xa2 : IsPerpendicular x a2 :=
by
  rw [IsPerpendicular]
  simp [x, a2]

theorem perp_xa3 : IsPerpendicular x a3 :=
by
  rw [IsPerpendicular]
  simp [x, a3]

-- rotation that takes x to y

def rotxyz_yxz : O3 :=
  {
    matrix := !![0, 1, 0 ; 1, 0, 0; 0, 0, 1],
    is_orth :=  by prove_orth
  }

def rotxyz_zyx : O3 :=
  {
    matrix := !![0, 0, 1 ; 0, 1, 0; 1, 0, 0],
    is_orth :=  by prove_orth
  }

def rotxyz_xzy : O3 :=
  {
    matrix := !![1, 0, 0 ; 0, 0, 1; 0, 1, 0],
    is_orth :=  by prove_orth
  }

def rotxyz_xmzmy : O3 :=
  {
    matrix := !![1, 0, 0 ; 0, 0, -1; 0, -1, 0],
    is_orth :=  by prove_orth
  }

set_option linter.unusedVariables false
theorem step_1 (f : OneZeroOneFunc):
  ∃ f : OneZeroOneFunc,  apply f x = zero :=
by
  have hin : [apply f x, apply f y, apply f z] ∈ ValidThriples := f.property x y z perp_xyz
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq => exact Exists.intro f heq.left
  | inr heq => cases heq with
    | inl heq =>
      apply Exists.intro (rotxyz_yxz.compose_OneZeroOneFunc f)
      rw [O3.compose_OneZeroOneFunc, apply] ; simp
      have hrotn : rotxyz_yxz.function x = y := by
        rw [O3.function, x, y] ; simp [rotxyz_yxz]; apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      rw [hrotn]
      exact heq.right.left
    | inr heq =>
      apply Exists.intro (rotxyz_zyx.compose_OneZeroOneFunc f)
      rw [O3.compose_OneZeroOneFunc, apply] ; simp
      have hrotn : rotxyz_zyx.function x = z := by
        rw [O3.function, x, z] ; simp [rotxyz_zyx]; apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      rw [hrotn]
      exact heq.right.right

theorem step_2 (f : OneZeroOneFunc) (hx : apply f x = zero) :
  ∃ f : OneZeroOneFunc, apply f x = zero ∧ apply f b1 = zero :=
by
  have ha2 : apply f a2 = one := by
    apply perp_zero_implies_one f x a2 hx perp_xa2
  have hin : [apply f a2, apply f b1, apply f b2] ∈ ValidThriples := f.property a2 b1 b2 perp_a2b1b2
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq =>
    rw [heq.left] at ha2
    contradiction
  | inr heq => cases heq with
    | inl heq =>
      exact Exists.intro f (And.intro hx heq.right.left)
    | inr heq =>
      apply Exists.intro (rotxyz_xmzmy.compose_OneZeroOneFunc f)
      repeat rw [O3.compose_OneZeroOneFunc] ; repeat rw [apply] ; simp
      have hrotxx : rotxyz_xmzmy.function x = x := by
        simp [O3.function, x, rotxyz_xmzmy, Matrix.vecHead, Matrix.vecTail]
        apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      have hrotb1b2 : rotxyz_xmzmy.function b1 = b2 := by
        simp [O3.function, b1, b2, rotxyz_xmzmy, Matrix.vecHead, Matrix.vecTail]
        apply Subtype.eq ; simp ; apply Iff.mp List.ofFn_inj ; simp ; norm_num
      rw [hrotxx, hrotb1b2]
      apply And.intro hx heq.right.right

theorem step_3 (f : OneZeroOneFunc) (hx : apply f x = zero) (hb1 : apply f b1 = zero) :
  ∃ f : OneZeroOneFunc, apply f x = zero ∧ apply f b1 = zero ∧ apply f b3 = zero :=
by
  have ha1 : apply f a1 = one := by
    apply perp_zero_implies_one f x a1 hx perp_xa1
  have hin : [apply f a1, apply f b3, apply f b4] ∈ ValidThriples := f.property a1 b3 b4 perp_a1b3b4
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq =>
    rw [heq.left] at ha1
    contradiction
  | inr heq => cases heq with
    | inl heq =>
      exact Exists.intro f (And.intro hx (And.intro hb1 heq.right.left))
    | inr heq =>
      apply Exists.intro (rotxyz_xzy.compose_OneZeroOneFunc f)
      repeat rw [O3.compose_OneZeroOneFunc] ; repeat rw [apply] ; simp
      have hrotxx : rotxyz_xzy.function x = x := by
        simp [O3.function, x, rotxyz_xzy, Matrix.vecHead, Matrix.vecTail]
        apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      have hrotb1b1 : rotxyz_xzy.function b1 = b1 := by
        simp [O3.function, b1, b2, rotxyz_xzy, Matrix.vecHead, Matrix.vecTail]
        apply Subtype.eq ; simp ; apply Iff.mp List.ofFn_inj ; simp
      have hrotb3b4 : rotxyz_xzy.function b3 = b4 := by
        simp [O3.function, b3, b4, rotxyz_xzy, Matrix.vecHead, Matrix.vecTail]
        apply Subtype.eq ; simp ; apply Iff.mp List.ofFn_inj ; simp
      rw [hrotxx, hrotb1b1, hrotb3b4]
      apply And.intro hx (And.intro hb1 heq.right.right)

-- noncomputable def x : MeasurementDirection := ⟨![1, 0, 0], by vec_norm⟩
-- noncomputable def y : MeasurementDirection := ⟨![0, 1, 0], by vec_norm⟩
-- noncomputable def z : MeasurementDirection := ⟨![0, 0, 1], by vec_norm⟩
-- noncomputable def a1 : MeasurementDirection := ⟨![0, 1 / √2, 1 / √2], by vec_norm⟩
-- noncomputable def a2 : MeasurementDirection := ⟨![0, -1 / √2, 1 / √2], by vec_norm⟩
-- noncomputable def a3 : MeasurementDirection := ⟨![0, -1 / √2, -1 / √2], by vec_norm⟩
-- noncomputable def b1 : MeasurementDirection := ⟨![1 / √2, 1 / 2, 1 / 2], by vec_norm⟩
-- noncomputable def b2 : MeasurementDirection := ⟨![1 / √2, -1 / 2, -1 / 2], by vec_norm⟩
-- noncomputable def b3 : MeasurementDirection := ⟨![1 / √2, -1 / 2, 1 / 2], by vec_norm⟩
-- noncomputable def b4 : MeasurementDirection := ⟨![1 / √2, 1 / 2, -1 / 2], by vec_norm⟩
noncomputable def c1 : MeasurementDirection := ⟨![-1 / √3, √2 / √3, 0], by vec_norm⟩
noncomputable def c2 : MeasurementDirection := ⟨![1 / √3, √2 / √3, 0], by vec_norm⟩
noncomputable def d1 : MeasurementDirection := ⟨![√2 / √3, 1 / √3, 0], by vec_norm⟩
noncomputable def d2 : MeasurementDirection := ⟨![√2 / √3, -1 / √3, 0], by vec_norm⟩
noncomputable def e1 : MeasurementDirection := ⟨![-1 / 2, 1 / √2, 1 / 2], by vec_norm⟩
noncomputable def e2 : MeasurementDirection := ⟨![-1 / 2, 1 / √2, -1 / 2], by vec_norm⟩
noncomputable def e3 : MeasurementDirection := ⟨![1 / 2, 1 / √2, 1 / 2], by vec_norm⟩
noncomputable def e4 : MeasurementDirection := ⟨![1 / 2, 1 / √2, -1 / 2], by vec_norm⟩
noncomputable def f1 : MeasurementDirection := ⟨![-1 / √2, 0, 1 / √2], by vec_norm⟩
noncomputable def f2 : MeasurementDirection := ⟨![1 / √2, 0, 1 / √2], by vec_norm⟩


theorem perp_c1zd1 : IsMutuallyPerpendicular c1 z d1 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [c1, z])
  apply And.intro (by simp [z,d1]) (by simp [c1, d1] ; ring_nf)

theorem perp_c2zd2 : IsMutuallyPerpendicular c2 z d2 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [c2, z])
  apply And.intro (by simp [z, d2]) (by simp [c2, d2] ; ring_nf)

theorem perp_e2e3f1 : IsMutuallyPerpendicular e2 e3 f1 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [e2, e3] ; field_simp ; ring)
  apply And.intro (by simp [e3, f1] ; ring_nf) (by simp [e2, f1] ; ring_nf)

theorem perp_e1e4f2 : IsMutuallyPerpendicular e1 e4 f2 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [e1, e4] ; field_simp ; ring)
  apply And.intro (by simp [e4, f2] ; ring_nf) (by simp [e1, f2] ; ring_nf)

theorem perp_b1c1 : IsPerpendicular b1 c1 :=
by
  rw [IsPerpendicular]
  simp [b1, c1] ; norm_num ; field_simp ; ring_nf ; norm_num

theorem perp_b3c2 : IsPerpendicular b3 c2 :=
by
  rw [IsPerpendicular]
  simp [b3, c2] ; norm_num ; field_simp ; ring_nf ; norm_num

theorem perp_xz : IsPerpendicular x z :=
by
  rw [IsPerpendicular]
  simp [x, z]

theorem perp_f1f2 : IsPerpendicular f1 f2 :=
by
  rw [IsPerpendicular]
  simp [f1, f2] ; field_simp

theorem perp_d1e1 : IsPerpendicular d1 e1 :=
by
  rw [IsPerpendicular]
  simp [d1, e1]  ; field_simp ; ring_nf ; norm_num ; ring

theorem perp_d2e3 : IsPerpendicular d2 e3 :=
by
  rw [IsPerpendicular]
  simp [d2, e3]  ; field_simp ; ring_nf ; norm_num ; ring

theorem perp_d1e2 : IsPerpendicular d1 e2 :=
by
  rw [IsPerpendicular]
  simp [d1, e2]  ; field_simp ; ring_nf ; norm_num ; ring

theorem perp_d2e4 : IsPerpendicular d2 e4 :=
by
  rw [IsPerpendicular]
  simp [d2, e4]  ; field_simp ; ring_nf ; norm_num ; ring

theorem step_4 (f : OneZeroOneFunc) (hx : apply f x = zero) (hb1 : apply f b1 = zero) (hb3 : apply f b3 = zero) :
  False :=
by
  have hz : apply f z = one := by
    apply perp_zero_implies_one f x z hx perp_xz
  have hc1 : apply f c1 = one := by
    apply perp_zero_implies_one f b1 c1 hb1 perp_b1c1
  have hc2 : apply f c2 = one := by
    apply perp_zero_implies_one f b3 c2 hb3 perp_b3c2
  have hd1 : apply f d1 = zero := by
    apply perp_one_one_implies_zero f c1 z d1 (And.intro hc1 hz) perp_c1zd1
  have hd2 : apply f d2 = zero := by
    apply perp_one_one_implies_zero f c2 z d2 (And.intro hc2 hz) perp_c2zd2
  have he1 : apply f e1 = one := by
    apply perp_zero_implies_one f d1 e1 hd1 perp_d1e1
  have he2 : apply f e2 = one := by
    apply perp_zero_implies_one f d1 e2 hd1 perp_d1e2
  have he3 : apply f e3 = one := by
    apply perp_zero_implies_one f d2 e3 hd2 perp_d2e3
  have he4 : apply f e4 = one := by
    apply perp_zero_implies_one f d2 e4 hd2 perp_d2e4
  have hf1 : apply f f1  = zero := by
    apply perp_one_one_implies_zero f e2 e3 f1 (And.intro he2 he3) perp_e2e3f1
  have hf2 : apply f f2  = zero := by
    apply perp_one_one_implies_zero f e1 e4 f2 (And.intro he1 he4) perp_e1e4f2
  have hf2_contradiction : apply f f2  = one := by
    apply perp_zero_implies_one f f1 f2 hf1 perp_f1f2

  rw [hf2] at hf2_contradiction
  contradiction

--TODO: is IsEmpty the right paradigm?
theorem kochen_specker :
  IsEmpty OneZeroOneFunc :=
by
  apply (Iff.mpr isEmpty_iff)
  intro f
  cases (step_1 f) with
  | intro f hx => cases (step_2 f hx) with
    | intro f hxb1 => cases (step_3 f hxb1.left hxb1.right) with
      | intro f hxb1b3 =>
        exact step_4 f hxb1b3.left hxb1b3.right.left hxb1b3.right.right

























#eval Matrix.vecHead ∘ ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]]









-- Now, need to figure out how to express compositions

-- def m : Matrix (Fin 2) (Fin 2) ℝ :=
--   Matrix.of (fun i j =>
--     match (i, j) with
--     | (0, 0) => 1/√2
--     | (0, 1) => -1/√2
--     | (1, 0) => 1/√2
--     | (1, 1) => 1/√2)
--  -- here's how we perform multiplication
-- #check Matrix.mulVec m ![0, 0]
-- #check m * ![1, 2]

-- -- here is a template to show membership within O3
-- theorem sanity_check : m ∈ O3 :=
-- by
--   apply (Iff.mpr (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ))
--   rw [star, Matrix.instStar] ; simp ;
--   ext i j
--   simp [Matrix.mul_apply]
--   fin_cases i <;> fin_cases j
--   all_goals {
--     simp [Matrix.transpose_apply, m] ; norm_num ; apply?
--   }



-- now we want to show O3 maintains dot product
-- #print Iff
-- #check star
-- #check (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ)
-- #check Matrix.orthogonalGroup (Fin 3) ℝ
-- #check norm_eq_sqrt_real_inner
-- #check inner
-- #check (WithLp.equiv 2 _ _).symm ![1, 2, 3]
-- #eval Matrix.dotProduct ![1, 2, 3] ![0, 1, 0]
-- #check Matrix.vecEmpty


end FreeWillLean
