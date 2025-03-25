import Mathlib

variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ}

noncomputable section
set_option maxHeartbeats 500000
set_option linter.unusedVariables false



lemma gcd_two (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ x y : ℤ, A 0 0 * x + A 1 0 * y = Int.gcd (A 0 0) (A 1 0)  := by
  let x := (A 0 0).gcdA (A 1 0)
  let y := (A 0 0).gcdB (A 1 0)
  have h : (A 0 0).gcd (A 1 0) = A 0 0 * x + A 1 0 * y :=  Int.gcd_eq_gcd_ab (A 0 0) (A 1 0)
  use x
  use y
  rw[← h]

lemma gcd_two_2 (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ z w : ℤ, A 0 1 * z + A 1 1 * w = Int.gcd (A 0 1) (A 1 1)  := by
  let z := (A 0 1).gcdA (A 1 1)
  let w := (A 0 1).gcdB (A 1 1)
  have h : (A 0 1).gcd (A 1 1) = A 0 1 * z + A 1 1 * w :=  Int.gcd_eq_gcd_ab (A 0 1) (A 1 1)
  use z
  use w
  rw[← h]



lemma gcd_four (A : Matrix (Fin 2) (Fin 2) ℤ) : ∃ a b : ℤ, Int.gcd (A 0 0) (A 1 0) * a + Int.gcd (A 0 1) (A 1 1) * b = Int.gcd (Int.gcd (A 0 0) (A 1 0)) (Int.gcd (A 0 1) (A 1 1)) := by
  let a := (Int.gcd (A 0 0) (A 1 0)).gcdA (Int.gcd (A 0 1) (A 1 1))
  let b := (Int.gcd (A 0 0) (A 1 0)).gcdB (Int.gcd (A 0 1) (A 1 1))
  have h : Int.gcd (Int.gcd (A 0 0) (A 1 0)) (Int.gcd (A 0 1) (A 1 1)) =
          Int.gcd (A 0 0) (A 1 0) * a + Int.gcd (A 0 1) (A 1 1) * b :=
    Int.gcd_eq_gcd_ab (Int.gcd (A 0 0) (A 1 0)) (Int.gcd (A 0 1) (A 1 1))
  use a
  use b
  rw[← h]



  def d1 (A :  Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
    Int.gcd (Int.gcd (A 0 0) (A 1 0)) (Int.gcd (A 0 1) (A 1 1))

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


lemma mat_pow_i (p n i : ℕ) [Fact p.Prime] (hi : i ≥ 1) : !![(p ^ (n * i) : ℤ), (i * p ^ (i * n - n) : ℤ ); (0 : ℤ), (p ^ (n * i) : ℤ)] * !![(p ^ n : ℤ), (1 : ℤ); (0 : ℤ), (p ^ n : ℤ)] = !![(p ^ (n * (i + 1)) : ℤ), ((i + 1) * p ^ ((i + 1) * n - n) : ℤ); (0 : ℤ), (p ^ (n * (i + 1)) : ℤ)] := by
  rw[@Matrix.mul_fin_two]
  repeat rw [mul_zero]
  repeat rw[zero_mul]
  repeat rw[zero_add]
  repeat rw[add_zero]
  repeat rw[mul_one]
  rw [Nat.right_distrib]
  rw [Int.add_mul]
  repeat rw [one_mul]
  have h1 : n * (i + 1) = n * i + n := by
    ring
  rw [h1]
  rw [pow_add]
  have h2 : (i * p ^ (i * n - n) * p ^ n : ℤ) = (i * p ^ (i * n - n + n) : ℤ) := by
    ring
  rw [h2]
  rw [add_comm]
  have h3 : i * n + n - n = n * i := by
    rw [Nat.add_sub_cancel]
    rw[mul_comm]
  rw [h3]
  have h4 : i * n - n + n = n * i  := by
    rw [Nat.sub_add_cancel]
    rw [mul_comm]
    exact Nat.le_mul_of_pos_left n hi
  rw [h4]


lemma MYmat_pow_1 (p n i : ℕ) [Fact p.Prime] (hi : i ≥ 1) : (MYmat p n) ^ i = !![(p ^ (n * i) : ℤ), (i * p ^ (i * n - n) : ℤ); (0 : ℤ), (p ^ (n * i) : ℤ)] := by
  induction i with
  | zero =>
    exfalso
    exact Nat.not_succ_le_zero 0 hi
  | succ i ih =>
    cases i with
    | zero =>
    simp
    rfl
    | succ i =>
    rw [pow_succ]
    rw [ih]
    rw [MYmat]
    rw [mat_pow_i]
    rfl
    exact Nat.le_add_left 1 i
    exact Nat.le_add_left 1 i
  #print axioms MYmat_pow_1


lemma gcd_of_ip_p_div {p n i : ℕ} [Fact p.Prime] (hi : i ≥ 1) (h : p ^ n ∣ i) : Int.gcd ((i : ℤ) * (p : ℤ) ^ (i * n - n)) (p ^ (n * i)) = p ^ (n * i) := by
  obtain ⟨k ,hk⟩ := h
  nth_rewrite 1 [hk]
  have h3 : p ^ n * k = k * p ^ n := by
    ring
  rw [h3]
  have h1 : (↑(k * p ^ n) * ↑p ^ (i * n - n) : ℤ).gcd (↑p ^ (n * i)) = (k * p ^ (n * i) : ℤ).gcd (p ^ (n * i) : ℤ) := by
    rw [←  Int.natCast_pow, ← Int.natCast_mul]
    simp
    have h1a : (↑k * ↑p ^ n * ↑p ^ (i * n - n) : ℤ) = ↑k * ↑p ^ (n * i) := by
      rw [← Int.natCast_pow, ← Int.natCast_mul]
      simp

      sorry
    rw [h1a]
  rw[h1]
  have h2 : (k * p ^ (n * i) : ℤ).gcd (p ^ (n * i)) = p ^ (n * i) * Int.gcd (k : ℤ) (1) := by

    sorry
  rw [h2]
  simp




lemma gcd_prime_pow (p a b : ℕ) [Fact p.Prime] : Int.gcd (p ^ a) (p ^ b) = p ^ (min a b) := by


  sorry


lemma d1_MYmat_pow_div (p n i : ℕ) [Fact p.Prime] (hi : i ≥ 1) (h : p ^ n ∣ i) : d1 ((MYmat p n) ^ i) = p ^ (n * i) := by
  rw[MYmat_pow_1]
  unfold d1
  simp
  have hgcd1 : Int.gcd (↑(i : ℤ) * (p : ℤ) ^ (i * n - n)) (↑p ^ (n * i)) = (p ^ (n * i)) := by
    apply gcd_of_ip_p_div
    exact hi
    exact h
  rw[hgcd1]
  simp at *
  exact hi


lemma d1_MYmat_pow_ndiv (p n i : ℕ) [Fact p.Prime] (hi : i ≥ 1) (h :  ¬ p ^ n ∣ i) : d1 ((MYmat p n) ^ i) = p ^ (n * i - n) := by
  rw[MYmat_pow_1]
  unfold d1
  simp
  have hgcd3 : Int.gcd (↑(i : ℤ) * (p : ℤ) ^ (i * n - n)) (↑p ^ (n * i)) = (p ^ (n * i - n)) := by
    sorry
  rw[hgcd3]

  sorry
  exact hi


lemma SNF_MYmat_1 (p n i : ℕ) [Fact p.Prime] (hp : p ≠ 0) (h : p ^ n ∣ i) (hi : i ≥ 1) : SNF ((MYmat p n) ^ i) = !![(p ^ (n * i) : ℤ), 0; 0, (p ^ (n * i) : ℤ)] := by
  rw [MYmat_pow_1, SNF]
  rw[d2']
  have h1 : !![(p ^ (n * i) : ℤ), (i * p ^ (i * n - n) : ℤ); 0, (p ^ (n * i) : ℤ)].det = (p ^ (2 *(n * i)) : ℤ) := by
    rw[Matrix.det_fin_two]
    simp
    ring
  rw [h1]
  rw [← MYmat_pow_1 p n i hi]
  rw [d1_MYmat_pow_div]
  have test : (p ^ (n * i) : ℤ) * (p ^ (n * i) : ℤ) / (p ^ (n * i) : ℤ) = (p ^ (n * i) : ℤ) * 1 := by
    refine Int.ediv_eq_of_eq_mul_right ?H1 ?H2
    · exact Ne.symm (NeZero.ne' (p ^ (n * i) : ℤ))
    · rw [mul_one]
  have h2 : (p ^ (2 * (n * i)) : ℤ) / (p ^ (n * i) : ℤ) = p ^ (n * i) := by
    rw [Nat.two_mul]
    rw [@npow_add]
    rw[test]
    rw[mul_one]
  rw[h2]
  exact hi
  exact h
  exact hi


lemma SNF_MYmat_2 (p n i : ℕ) [Fact p.Prime] (hp : p ≠ 0) (h :  ¬ p ^ n ∣ i) (hi : i ≥ 1) : SNF ((MYmat p n) ^ i) = !![(p ^ (n * i - n) : ℤ), 0; 0, (p ^ (n * i + n) : ℤ)] := by
  rw [MYmat_pow_1, SNF]
  rw[d2']
  have h1 : !![(p ^ (n * i) : ℤ), (i * p ^ (i * n - n) : ℤ); 0, (p ^ (n * i) : ℤ)].det = (p ^ (2 *(n * i)) : ℤ) := by
    rw[Matrix.det_fin_two]
    simp
    ring
  rw[h1]
  rw [← MYmat_pow_1 p n i hi]
  rw [d1_MYmat_pow_ndiv]
  have h2' : n * i - n + (n * i + n) = 2 * (n * i) := by
    rw [Nat.add_left_comm]
    rw [Nat.sub_add_cancel]
    rw [mul_comm]
    rw [Nat.two_mul]
    exact Nat.le_mul_of_pos_right n hi
  have h2 : (p ^ ( 2 * (n * i)) : ℤ) / (p ^ (n * i - n) : ℤ) = p ^ (n * i + n) := by
    rw[Int.ediv_eq_of_eq_mul_right]
    norm_cast
    exact pow_ne_zero (n * i - n) hp
    rw[← pow_add]
    rw[h2']
  rw[h2]
  exact hi
  exact h
  exact hi

def C2 (p n : ℕ) [Fact p.Prime] : Matrix (Fin 2) (Fin 2) ℤ := !![p^(p*n), 0; 0, p^(p*n)]

def C (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 0; 0, b]

def Vp (p : ℕ) (a : ℤ) [Fact p.Prime] : ℕ := padicValInt p a

def MatrixValuation_2 (p : ℕ) [Fact p.Prime] (M : Matrix (Fin 2) (Fin 2) ℤ) :=
  !![(Vp p (M 0 0)), Vp p (M 0 1) ; Vp p (M 1 0), Vp p (M 1 1)]

def MatrixValuation_1 (p : ℕ) [Fact p.Prime] (M : Matrix (Fin 2) (Fin 2) ℤ) :=
  !![(Vp p (d1 M)), 0 ; 0, Vp p (d2' M)]

def val_pow  (a : ℕ) (p : ℕ) [Fact p.Prime] : Vp p (p ^ a) = a := by
  rw [Vp]
  rw [padicValInt]
  have h : ((p : ℤ) ^ a).natAbs = p ^ a
  · rw [Int.natAbs_pow, Int.natAbs_ofNat]
  rw [h]
  exact padicValNat.prime_pow a

def Vp_of_0 (p : ℕ) [Fact p.Prime] : Vp p 0 = 0 := by
  rw [Vp]
  rw [padicValInt]
  simp

--2x2 case of the conjecture

def padic_valuation_SNF_conjecture (p n N i : ℕ) [Fact p.Prime] (hn : n > 0) (hN : N > 0) (A : Matrix (Fin 2) (Fin 2) ℤ) : Prop := ∃ (d : ℕ) (hd : d > 0) (C : Matrix (Fin 2) (Fin 2) ℤ), ∀ i (hi : i > 0),
  MatrixValuation_2 p (SNF (A ^ (i + d * N))) = MatrixValuation_2 p (C^N) + MatrixValuation_2 p (SNF (A^i))

-- D_i+dn with p ^ n ∣ i

lemma MYmat_dn (p n i N : ℕ) [Fact p.Prime] (hi : i > 0) (hN : N > 0) :
  (MYmat p n) ^ (i + p * N) = !![(p ^ (n * (i + p * N)) : ℤ), ((i + p * N) * p ^ ((i + p * N) * n - n) : ℤ); (0 : ℤ), (p ^ (n * (i + p * N)) : ℤ)] := by
  sorry

  lemma d1_MYmat_dn (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) :
    d1 ((MYmat p n) ^ (i + p * N)) = p ^ (n * (i + p * N)) := by
    sorry

lemma SNF_MYmat_dn (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) (hp : p ≠ 0) (hd : p ^ n ∣ i) : SNF ((MYmat p n) ^ (i + p * N)) = !![(p ^ (n * (i + p * N)) : ℤ), 0; 0, (p ^ (n * (i + p * N)) : ℤ)] := by
  rw [MYmat_pow_1, SNF]
  rw [d2']
  have hdet : !![(p ^ (n * (i + p * N)) : ℤ), ((i + p * N) * ↑p ^ ((i + p * N) * n - n) : ℤ); 0 , (p ^ (n * (i + p * N)) : ℤ)].det = (p ^ (2 * (i + p * N) * n) : ℤ):= by
    rw [Matrix.det_fin_two]
    simp
    ring
  sorry
  exact Nat.le_add_right_of_le hi



def C2_N (p n N : ℕ) [Fact p.Prime] (hN : N > 0) : (C2 p n) ^ N = !![(p ^ (p * n * N) : ℤ), 0; 0, (p ^ (p * n * N) : ℤ)] := by
  induction N with
  | zero =>
    exfalso
    exact Nat.not_succ_le_zero 0 hN
  | succ N iN =>
    cases N with
    | zero =>
    simp
    rfl
    | succ N =>
    rw [pow_succ]
    rw [iN]
    rw [C2]
    simp
    ring_nf
    exact Nat.zero_lt_succ N
  #print axioms C2_N

-- padic valuation of D_i with p ^ n ∣ i

def Valuation_of_SNF_MYmat_1 (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) (hp : p ≠ 0) (hd : p ^ n ∣ i) : MatrixValuation_2 p (SNF ((MYmat p n) ^ i)) = !![n * i, 0; 0, n * i] := by
  rw [SNF_MYmat_1 p n i hp hd hi]
  rw[MatrixValuation_2]
  rw [Vp]
  simp
  have h : Vp p 0 = 0 := by
    exact Vp_of_0 p
  repeat rw [h]
  have h1 :  Vp p (p ^ (n * i)) = n * i := by
    rw [val_pow]
  rw [h1]
  have h2 : padicValInt p (↑p ^ (n * i)) = n * i := by
    rw [padicValInt]
    rw [Int.natAbs_pow, Int.natAbs_ofNat]
    exact padicValNat.prime_pow (n * i)
  rw [h2]
-- padic valuation of D_i+dn with p ^ n ∣ i

  def Valuation_of_SNF_MYmat_dn (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) (hp : p ≠ 0) (hd : p ^ n ∣ i) : MatrixValuation_2 p (SNF ((MYmat p n) ^ (i + p * N))) = !![n * (i + p * N), 0; 0, n * (i + p * N)] := by
    rw [SNF_MYmat_dn p n i N hn hi hN hp hd]
    rw [MatrixValuation_2]
    rw [Vp]
    simp
    have h : Vp p 0 = 0 := by
      exact Vp_of_0 p
    repeat rw [h]
    have h1 : Vp p (p ^ (n * (i + p * N))) = n * (i + p * N) := by
      rw [val_pow]
    rw [h1]
    have h2 : padicValInt p (↑p ^ (n * (i + p * N))) = n * (i + p * N) := by
      rw [padicValInt]
      rw [Int.natAbs_pow, Int.natAbs_ofNat]
      exact padicValNat.prime_pow (n * (i + p * N))
    rw [h2]

def Valuation_of_C2_N (p n N : ℕ) [Fact p.Prime] (hN : N > 0) : MatrixValuation_2 p ((C2 p n) ^ N) = !![p * n * N, 0; 0, p * n * N] := by
  rw [C2_N]
  rw [MatrixValuation_2]
  rw [Vp]
  simp
  have h : Vp p 0 = 0 := by
    exact Vp_of_0 p
  repeat rw [h]
  have h1 : Vp p (p ^ (p * n * N)) = p * n * N := by
    rw [val_pow]
  rw [h1]
  have h2 : padicValInt p (p ^ (p * n * N)) = p * n * N := by
    rw [padicValInt]
    rw [Int.natAbs_pow, Int.natAbs_ofNat]
    exact padicValNat.prime_pow (p * n * N)
  rw [h2]
  exact hN
-- specific 2x2 case for when p ^ n ∣ i

theorem Theorem_div (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) (hp : p ≠ 0) (hd : p ^ n ∣ i) :
  MatrixValuation_2 p (SNF ((MYmat p n) ^ (i + p * N))) =
  MatrixValuation_2 p ((C2 p n) ^ N) + MatrixValuation_2 p (SNF ((MYmat p n) ^ i)) := by
  rw [Valuation_of_C2_N]
  rw [Valuation_of_SNF_MYmat_dn]
  rw [Valuation_of_SNF_MYmat_1]
  rw [Matrix.add]
  simp
  have h1 : p * n * N + n * i = n * (i + p * N) := by ring
  rw [h1]
  exact p
  exact hn
  exact hi
  exact Nat.zero_lt_of_ne_zero hp
  exact hp
  exact hd
  exact hn
  exact hi
  exact hN
  exact hp
  exact hd
  exact hN


lemma mat_pow_p (p n : ℕ) [Fact p.Prime] (hp : p ≥ 1) :
  !![(p ^ (n * p) : ℤ), (p * p ^ (p * n - n) : ℤ); (0 : ℤ), (p ^ (n * p) : ℤ)] *
  !![(p ^ n : ℤ), (1 : ℤ); (0 : ℤ), (p ^ n : ℤ)] =
  !![(p ^ (n * (p + 1)) : ℤ), ((p + 1) * p ^ ((p + 1) * n - n) : ℤ); (0 : ℤ), (p ^ (n * (p + 1)) : ℤ)] := by
  rw[@Matrix.mul_fin_two]
  repeat rw [mul_zero]
  repeat rw[zero_mul]
  repeat rw[zero_add]
  repeat rw[add_zero]
  repeat rw[mul_one]
  rw [Nat.right_distrib]
  rw [Int.add_mul]
  repeat rw [one_mul]
  have h1 : n * (p + 1) = n * p + n := by
    ring
  rw [h1]
  rw [pow_add]
  have h2 : (p * p ^ (p * n - n) * p ^ n : ℤ) = (p * p ^ (p * n - n + n) : ℤ) := by
    ring
  rw [h2]
  rw [add_comm]
  have h3 : p * n + n - n = n * p := by
    rw [Nat.add_sub_cancel]
    rw[mul_comm]
  rw [h3]
  have h4 : p * n - n + n = n * p := by
    rw [Nat.sub_add_cancel]
    rw [mul_comm]
    exact Nat.le_mul_of_pos_left n hp
  rw [h4]





def SNF_MYmat_2_dn (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) (hp : p ≠ 0) (hd : ¬ p ^ n ∣ i) : SNF ((MYmat p n) ^ (i + p * N)) = !![(p ^ ( n * (i + p * N) - n ) : ℤ), 0; 0, (p ^ ( n * (i + p * N) + n) : ℤ)] := by

  sorry

def Valuation_of_SNF_MYmat_2_dn (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) (hp : p ≠ 0) (hd : ¬ p ^ n ∣ i) : MatrixValuation_2 p (SNF ((MYmat p n) ^ (i + p * N))) = !![n * (i + p * N) - n, 0; 0, n * (i + p * N) + n] := by
  rw [SNF_MYmat_2_dn p n i N hn hi hN hp hd]
  rw [MatrixValuation_2]
  rw [Vp]
  simp
  have h : Vp p 0 = 0 := by
    exact Vp_of_0 p
  repeat rw [h]
  have h1 : Vp p (p ^ (n * (i + p * N) - n)) = n * (i + p * N) - n := by
    rw [val_pow]
  have h2 : Vp p (p ^ (n * (i + p * N) + n)) = n * (i + p * N) + n := by
    rw [val_pow]
  rw [h2]
  have h1 : padicValInt p (p ^ (n * (i + p * N) - n)) = (n * (i + p * N) - n) := by
    rw [padicValInt]
    rw [Int.natAbs_pow, Int.natAbs_ofNat]
    exact padicValNat.prime_pow (n * (i + p * N) - n)
  rw [h1]


def Valuation_of_SNF_MYmat_2 (p n i : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hp : p ≠ 0) (hd : ¬ p ^ n ∣ i) : MatrixValuation_2 p (SNF ((MYmat p n) ^ i)) = !![n * i - n, 0; 0, n * i + n] := by
  rw [SNF_MYmat_2 p n i hp hd hi]
  rw [MatrixValuation_2]
  rw [Vp]
  simp
  have h : Vp p 0 = 0 := by
    exact Vp_of_0 p
  repeat rw [h]
  have h2 : Vp p (p ^ (n * i + n)) = n * i + n := by
    rw [val_pow]
  rw [h2]
  have h1 : padicValInt p (p ^ (n * i - n)) = n * i - n := by
    rw[padicValInt]
    rw [Int.natAbs_pow, Int.natAbs_ofNat]
    exact padicValNat.prime_pow (n * i - n)
  rw [h1]



-- 2 x 2 case with p ^ n ∤ i
theorem Theorem_ndiv (p n i N : ℕ) [Fact p.Prime] (hn : n > 0) (hi : i > 0) (hN : N > 0) (hp : p ≠ 0) (hd : ¬ p ^ n ∣ i) :
  MatrixValuation_2 p (SNF ((MYmat p n) ^ (i + p * N))) =
  MatrixValuation_2 p ((C2 p n) ^ N) + MatrixValuation_2 p (SNF ((MYmat p n) ^ i)) := by
  rw[Valuation_of_C2_N]
  rw[Valuation_of_SNF_MYmat_2_dn]
  rw[Valuation_of_SNF_MYmat_2]
  rw[Matrix.add]
  simp
  have h1 : n * (i + p * N) - n = p * n * N + (n * i - n) := by
    ring_nf
    rw [Nat.add_comm]
    refine Nat.add_sub_assoc ?h (n * p * N)
    exact Nat.le_mul_of_pos_right n hi
  have h2 : n * (i + p * N) + n = p * n * N + (n * i + n) := by
    ring_nf
  rw[h1, h2]
  exact hn
  exact hi
  exact hp
  exact hd
  exact hn
  exact hi
  exact hN
  exact hp
  exact hd
  exact hN




#min_imports
