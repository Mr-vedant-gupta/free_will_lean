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


def MeasurementDirection : Type :=
  {v : EuclideanSpace ℝ (Fin 3) // ‖v‖ = 1}

def MeasurementDirection.index (d : MeasurementDirection) (i : Fin 3) : ℝ :=
  d.val i

notation d "[" i "]" => MeasurementDirection.index d i

noncomputable def v1 : MeasurementDirection := ⟨!₂[1/√3, 1/√3, 1/√3], by
  simp [EuclideanSpace.norm_eq] ;
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]; simp ; norm_num⟩

def v2 : MeasurementDirection := ⟨!₂[1, 0, 0], by
  simp [EuclideanSpace.norm_eq] ;
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]; norm_num⟩

/-TODO: ideally use the mathlib definition here instead-/
def DotProduct (x y : MeasurementDirection):=
  (x[0]) * (y[0]) + (x[1]) * (y[1]) + (x[2]) * (y[2])

def IsPerpendicular (d1 d2 : MeasurementDirection) : Prop :=
  DotProduct d1 d2 = 0

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
  have hnorm : ‖v.val‖ = 1 := by apply v.2
  rw [EuclideanSpace.norm_eq] at hnorm
  simp at hnorm
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at hnorm
  simp at hnorm
  rw [MeasurementDirection.index, MeasurementDirection.index, MeasurementDirection.index]
  calc
    v.val 0 ^ 2 + v.val 1 ^ 2 + v.val 2 ^ 2 = v.val 0 ^ 2 + (v.val 1 ^ 2 + v.val 2 ^ 2) := by ring
    _ = 1 := by exact hnorm

def CompleteBasis (d1 d2 : MeasurementDirection) (hperp : IsPerpendicular d1 d2): MeasurementDirection :=
  ⟨!₂[d1[1] * d2[2] - d1[2] * d2[1], d1[2] * d2[0] - d1[0] * d2[2], d1[0] * d2[1] - d1[1] * d2[0]], by
    rw [norm, PiLp.instNorm] ; simp
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] ; simp ; ring_nf
    rw [IsPerpendicular, DotProduct] at hperp

    let a := d1[0]
    let b := d1[1]
    let c := d1[2]
    let x := d2[0]
    let y := d2[1]
    let z := d2[2]

    have hnd1 : a^2 + b^2 + c^2 = 1 := norm_def d1
    have hnd2 : x^2 + y^2 + z^2 = 1 := norm_def d2

    have hab : a^2 + b^2 = 1 - c^2 := by rw [←hnd1] ; ring
    have hbc : b^2 + c^2 = 1 - a^2 := by rw [←hnd1] ; ring
    have hca : c^2 + a^2 = 1 - b^2 := by rw [←hnd1] ; ring
    calc
      (-(b * z * c * y * 2) - b * y * x * a * 2 + b ^ 2 * z ^ 2 +
      (b ^ 2 * x ^ 2 - z * c * x * a * 2) + z ^ 2 * a ^ 2 + c ^ 2 * y ^ 2 +
      c ^ 2 * x ^ 2 + y ^ 2 * a ^ 2) ^ ((1 / 2) : ℝ) =
      (x ^ 2 * (b ^ 2 + c ^ 2) + y ^ 2 * (c ^ 2 + a ^ 2) + z ^ 2 * (a ^ 2 + b ^ 2)
      - (2 * b * z * c * y + 2 * b * y * x * a + 2 * z * c * x * a)) ^ ((1 / 2) : ℝ)  := by ring_nf
      _ = (x ^ 2 * (1 - a ^ 2) + y ^ 2 * (1 - b ^ 2) + z ^ 2 * (1 - c ^ 2)
      - (2 * b * z * c * y + 2 * b * y * x * a + 2 * z * c * x * a)) ^ ((1 / 2) : ℝ) := by rw [hab, hbc, hca]
      _ = (x ^ 2 + y ^ 2 + z ^ 2 - (a * x + b * y + c * z) ^ 2) ^ ((1 / 2) : ℝ) := by ring_nf
      _ = 1 := by rw [hnd2, hperp] ; simp⟩



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
    rw [IsPerpendicular, CompleteBasis, DotProduct] ; simp [MeasurementDirection.index] ; ring
  have hperp23 : IsPerpendicular d2 (CompleteBasis d1 d2 hperp12) := by
    rw [IsPerpendicular, CompleteBasis, DotProduct] ; simp [MeasurementDirection.index] ; ring
  have hmutualperp : IsMutuallyPerpendicular d1 d2 (CompleteBasis d1 d2 hperp12) := by
    rw [IsMutuallyPerpendicular]
    apply And.intro hperp12 (And.intro hperp23 hperp13)
  have hvalidthrip : [apply f d1, apply f d2, apply f (CompleteBasis d1 d2 hperp12)] ∈ ValidThriples :=
    f.2 d1 d2 (CompleteBasis d1 d2 hperp12) hmutualperp
  rw [hd1z] at hvalidthrip
  apply valid_measurements_starting_zero
  exact hvalidthrip




end FreeWillLean
