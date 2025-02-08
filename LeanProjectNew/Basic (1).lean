import Mathlib

variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ}

noncomputable section

--def A (a : ℤ) := !![a,1 ; 0,a]

--example (a : ℤ) : (A a).det = a*a - 1*0 := by exact Matrix.det_fin_two (A a)
/-
def d1 (A :  Matrix (Fin 2) (Fin 2) ℤ_[p]) : ℤ_[p] := by sorry

example (a b : ℤ_[p]) : ℤ_[p] := gcd a b


lemma d1_bezout (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) : ∃ x y z w : ℤ_[p], d1 A = x * A 0 0 + y * A 1 0
  + z * A 0 1 + w* A 1 1 := by sorry

lemma det_div_d1 (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) : ∃ u : ℤ_[p], A.det = d1 A * u := by sorry

def d2 (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) : ℤ_[p] := by
  have := det_div_d1 A
  have u := this.choose
  use u
  apply u.2

lemma d2_eq (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) : A.det = d1 A * d2 A := by
  rw [d2]
  exact (det_div_d1 A).choose_spec

def d2' (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) : ℚ_[p] := A.det / d1 A


def M (p n : ℕ) [Fact p.Prime] : Matrix (Fin 2) (Fin 2) ℤ_[p] := !![p^n,1;0,p^n]

example : (M p n).det = p^(2*n) := by
  rw [Matrix.det_fin_two]
  rw [M]
  simp
  ring


 -/

--IsBezout.gcd_eq_sum


lemma gcd_two (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ x y : ℤ, A 0 0 * x + A 1 0 * y = gcd (A 0 0) (A 1 0)  := by
let x := (A 0 0).gcdA (A 1 0)
let y := (A 0 0).gcdB (A 1 0)
have h : (A 0 0).gcd (A 1 0) = A 0 0 * x + A 1 0 * y :=  Int.gcd_eq_gcd_ab (A 0 0) (A 1 0)
use x
use y
rw[← h]
rfl

lemma gcd_two_2 (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ z w : ℤ, A 0 1 * z + A 1 1 * w = gcd (A 0 1) (A 1 1)  := by
let z := (A 0 1).gcdA (A 1 1)
let w := (A 0 1).gcdB (A 1 1)
have h : (A 0 1).gcd (A 1 1) = A 0 1 * z + A 1 1 * w :=  Int.gcd_eq_gcd_ab (A 0 1) (A 1 1)
use z
use w
rw[← h]
rfl


lemma gcd_four (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ a b : ℤ, gcd (A 0 0) (A 1 0) * a + gcd (A 0 1) (A 1 1) * b = gcd (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1)) := by
let a := (gcd (A 0 0) (A 1 0)).gcdA (gcd (A 0 1) (A 1 1))
let b := (gcd (A 0 0) (A 1 0)).gcdB (gcd (A 0 1) (A 1 1))
have h : gcd (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1)) =
         gcd (A 0 0) (A 1 0) * a + gcd (A 0 1) (A 1 1) * b :=
  Int.gcd_eq_gcd_ab (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1))
use a
use b
rw[← h]







def d1 (A :  Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  gcd (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1))

example (a b : ℤ) : ℤ := gcd a b


lemma d1_bezout (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ x y z w : ℤ, d1 A = A 0 0 * x + A 1 0 * y + A 0 1 * z + A 1 1 * w := by
obtain ⟨x, y, h1⟩ := gcd_two A
obtain ⟨z, w, h2⟩ := gcd_two_2 A
obtain ⟨a, b, h3⟩ := gcd_four A
rw[d1]
rw[← h1, ← h2] at h3
use (a * x), (a * y), (b * z), (b * w)
repeat rw[← mul_assoc]
symm at h1 h2
rw[h1, h2, ←h3]
have h3' : (A 0 0 * x + A 1 0 * y) * a + (A 0 1 * z + A 1 1 * w) * b = A 0 0 * a * x + A 1 0 * a * y + A 0 1 * b * z + A 1 1 * b * w := by
  ring
rw[h3']



lemma det_div_d1 (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ u : ℤ, A.det = d1 A * u := by
obtain ⟨x, y, z, bezout_eq⟩ := d1_bezout A
rw[Matrix.det_fin_two]
let h := A 0 0 * A 1 1 - A 0 1 * A 1 0
have h1 : (d1 A) ∣ A 0 0 := by
  unfold d1
  apply dvd_trans (gcd_dvd_left (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1)))
  apply gcd_dvd_left (A 0 0) (A 1 0)
have h1b : (d1 A) ∣ A 1 0 := by
  unfold d1
  apply dvd_trans (gcd_dvd_left (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1)))
  apply gcd_dvd_right (A 0 0) (A 1 0)
have h1c : (d1 A) ∣ A 0 1 := by
  unfold d1
  apply dvd_trans (gcd_dvd_right (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1)))
  apply gcd_dvd_left (A 0 1) (A 1 1)
have h1d : (d1 A) ∣ A 1 1 := by
  unfold d1
  apply dvd_trans (gcd_dvd_right (gcd (A 0 0) (A 1 0)) (gcd (A 0 1) (A 1 1)))
  apply gcd_dvd_right (A 0 1) (A 1 1)
have h2 : (d1 A) ∣ (A 0 0 * A 1 1) := by
  exact Dvd.dvd.mul_right h1 (A 1 1)
have h3 : (d1 A) ∣ (A 0 1 * A 1 0) := by
  exact Dvd.dvd.mul_right h1c (A 1 0)
have h4 : (d1 A) ∣ A.det := by
  rw [Matrix.det_fin_two]
  exact Int.dvd_sub h2 h3
rw [Int.dvd_def] at h4
use A.det / d1 A
have h5 : A.det = d1 A * (A.det / d1 A) := by
  rw [mul_comm]
  exact Eq.symm (Int.ediv_mul_cancel h4)
rw[← h5]
rw [Matrix.det_fin_two]





def det_nz (A : Matrix (Fin 2) (Fin 2) ℤ) := (A : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0

def d2 (A : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := by
  have := det_div_d1 A
  have u := this.choose
  use u

lemma d1_neq (A : Matrix (Fin 2) (Fin 2) ℤ) (hd : det_nz A) : d1 A ≠ 0 := by
have h := det_div_d1 A
obtain ⟨u, hu⟩ := h
intro h1
rw[h1, zero_mul] at hu
apply hd at hu
exact hu




lemma d2_eq (A : Matrix (Fin 2) (Fin 2) ℤ) : A.det = d1 A * d2 A := by
  rw [d2]
  exact (det_div_d1 A).choose_spec

def d2_equal (A : Matrix (Fin 2) (Fin 2) ℤ) := A.det / d1 A


def d2' (A : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := A.det / d1 A

lemma d2'_eq_d2 (A : Matrix (Fin 2) (Fin 2) ℤ) (hd : det_nz A) : d2 A = d2' A := by
unfold d2 d2'
have h := det_div_d1 A
have u := h.choose_spec
refine Int.eq_ediv_of_mul_eq_right ?H1 (id (Eq.symm u))
exact d1_neq A hd







def M (p n : ℕ) [Fact p.Prime] : Matrix (Fin 2) (Fin 2) ℤ := !![p^n,1;0,p^n]

example : (M p n).det = p^(2*n) := by
  rw [Matrix.det_fin_two]
  rw [M]
  simp
  ring

example (a : ℕ) (p : ℕ) [Fact p.Prime] : padicValInt p (p ^ a) = a := by
  rw [padicValInt]
  have h : ((p : ℤ) ^ a).natAbs = p ^ a
  · rw [Int.natAbs_pow, Int.natAbs_ofNat]
  rw [h]
  exact padicValNat.prime_pow a
  --show ((p : ℤ) ^ a).natAbs = p ^ a

example (a : ℕ) (p : ℕ) [Fact p.Prime] : padicValNat p (p ^ a) = a := by
  exact padicValNat.prime_pow a



def SNF (M : Matrix (Fin 2) (Fin 2) ℤ) := !![d1 M, 0; 0, d2' M]

def MYmat (p n : ℕ) [Fact p.Prime] : Matrix (Fin 2) (Fin 2) ℤ := !![p^n,1;0,p^n]

lemma Mymat_pow (p n i : ℕ) [Fact p.Prime] : (MYmat p n) ^ i = !![(p^(n*i) : ℤ), (i*p^(i*n-n) : ℤ); (0 : ℤ), (p^(n*i) : ℤ)] := by
  cases i with
  | zero =>
    exfalso -- case o i = 0 not possible
    sorry
  | succ k =>
    cases k with
    | zero =>
      simp
      rfl
    | succ n =>
      simp
      sorry











def Vp (p : ℕ) [Fact p.Prime] (x : ℤ) : ℕ := padicValInt p x


def conjecture (p : ℕ) [Fact p.Prime]: Prop :=

sorry




#min_imports
