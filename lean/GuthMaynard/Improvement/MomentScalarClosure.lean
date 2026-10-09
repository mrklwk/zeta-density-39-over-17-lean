module
public import GuthMaynard.Improvement.SpectralScaleBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Elementary absorption of the normalized cubic inequality. No positive
lower bound on the mass or reference scale is assumed. -/
theorem normalized_moment_absorption {M P Q : ℝ}
    (hM : 0 ≤ M) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : M^3 ≤ Q*(P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M)) :
    M ≤ (1+3*Q)*P := by
  by_cases hMP : M ≤ P
  · nlinarith [mul_nonneg hQ hP]
  · have hm : 0 < M := lt_of_le_of_lt hP (lt_of_not_ge hMP)
    have hpm : P ≤ M := (lt_of_not_ge hMP).le
    have hs : Real.sqrt P ≤ Real.sqrt M := Real.sqrt_le_sqrt hpm
    have hmid : P*Real.sqrt P*M*Real.sqrt M ≤ P*M^2 := by
      calc
        _ ≤ P*Real.sqrt M*M*Real.sqrt M := by gcongr
        _ = P*M*(Real.sqrt M)^2 := by ring
        _ = P*M^2 := by rw [Real.sq_sqrt hM]; ring
    have h1 : P^3 ≤ P*M^2 := by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP hpm 2) hP
      convert hh using 1
      ring
    have h2 : P^2*M ≤ P*M^2 := by
      have hh := mul_le_mul_of_nonneg_left hpm (mul_nonneg hP hM)
      nlinarith
    have hh : M^3 ≤ 3*Q*P*M^2 := by
      calc
        _ ≤ Q*(P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M) := h
        _ ≤ Q*(3*(P*M^2)) := mul_le_mul_of_nonneg_left (by linarith) hQ
        _ = _ := by ring
    have hcancel : M ≤ 3*Q*P := by
      have hh' : M*M^2 ≤ (3*Q*P)*M^2 := by convert hh using 1; ring
      exact le_of_mul_le_mul_right hh' (show 0 < M^2 by positivity)
    nlinarith

/-- A normalized subpower loss survives scalar absorption without enlargement. -/
theorem normalized_moment_power_absorption {M P Q N ε : ℝ}
    (hM : 0 ≤ M) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hN : 1 ≤ N) (hε : 0 ≤ ε)
    (h : M^3 ≤ Q*N^ε*(P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M)) :
    M ≤ (1+3*Q)*N^ε*P := by
  have hn : 0 ≤ N := by linarith
  have hp : 1 ≤ N^ε := Real.one_le_rpow hN hε
  have hh := normalized_moment_absorption hM hP (mul_nonneg hQ (Real.rpow_nonneg hn _)) h
  have hb : (1+3*(Q*N^ε))*P ≤ (1+3*Q)*N^ε*P := by
    apply mul_le_mul_of_nonneg_right _ hP
    nlinarith
  exact hh.trans hb

/-- Uniform normalized absorption: the chosen constant precedes every mass,
reference scale and large parameter. -/
theorem normalized_moment_uniform {ε Q : ℝ} (hε : 0 < ε) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M P : ℝ, 1 ≤ N → 0 ≤ M → 0 ≤ P →
      M^3 ≤ Q*N^ε*(P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M) →
      M ≤ C*N^ε*P := by
  refine ⟨1+3*Q,by positivity,?_⟩
  intro N M P hN hM hP hh
  exact normalized_moment_power_absorption hM hP hQ hN hε.le hh

/-- Normalize the middle-scale raw moment from explicit scalar identities and
three independent losses. Every constant is independent of the varying scales. -/
theorem raw_moment_normalized_budget {N L T P M H S C D K A B F X Y Z R : ℝ}
    (hN : 0 ≤ N) (hNL : N ≤ L) (hT : 0 ≤ T) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hS : 0 ≤ S) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hZ : 1 ≤ Z)
    (hH0 : 0 ≤ H) (hH : H ≤ K*X*N*L) (hR : R ≤ A*Y)
    (hlog : (Real.log (2*N))^2 ≤ B*Z)
    (hid : N^5*L*T=P^2) (htail : N^7*T^3 ≤ P^3)
    (hraw : M^3 ≤ S*F*(125*P^3+C*R*
      (5*P*Real.sqrt P*M*Real.sqrt M+5*D*N^4*T*(N^2+H)*M+
        3060*D*N^7*T^3*(Real.log (2*N))^2)+25*P^2*M)) :
    M^3 ≤ (S*(150+C*A*(5+5*D*(1+K)+3060*D*B)))*F*X*Y*Z*
      (P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M) := by
  have hL : 0 ≤ L := hN.trans hNL
  have hx : 0 ≤ X := by linarith
  have hy : 0 ≤ Y := by linarith
  have hz : 0 ≤ Z := by linarith
  let V := P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M
  have hv : 0 ≤ V := by dsimp [V]; positivity
  have hv10 : 0 ≤ P^3 := by positivity
  have hv20 : 0 ≤ P*Real.sqrt P*M*Real.sqrt M := by positivity
  have hv30 : 0 ≤ P^2*M := by positivity
  have hv1 : P^3 ≤ V := by dsimp [V]; linarith only [hv20,hv30]
  have hv2 : P*Real.sqrt P*M*Real.sqrt M ≤ V := by dsimp [V]; linarith only [hv10,hv30]
  have hv3 : P^2*M ≤ V := by dsimp [V]; linarith only [hv10,hv20]
  have hnx : N^2+H ≤ (1+K)*X*N*L := by
    have h1 := mul_le_mul_of_nonneg_left hNL hN
    have h2 := mul_le_mul_of_nonneg_right hX (mul_nonneg hN hL)
    nlinarith only [h1,h2,hH]
  have hm : 5*D*N^4*T*(N^2+H)*M ≤ 5*D*(1+K)*X*(P^2*M) := by
    calc
      _ ≤ 5*D*N^4*T*((1+K)*X*N*L)*M := by gcongr
      _ = _ := by rw [← hid]; ring
  have hb : 3060*D*N^7*T^3*(Real.log (2*N))^2 ≤ 3060*D*B*Z*P^3 := by
    calc
      _ = 3060*D*(N^7*T^3)*(Real.log (2*N))^2 := by ring
      _ ≤ 3060*D*P^3*(B*Z) := by gcongr
      _ = _ := by ring
  have hvx : V ≤ X*V := le_mul_of_one_le_left hv hX
  have hvz : V ≤ Z*V := le_mul_of_one_le_left hv hZ
  have hvxz : V ≤ X*Z*V := by
    calc
      V ≤ X*V := hvx
      _ ≤ X*(Z*V) := mul_le_mul_of_nonneg_left hvz hx
      _ = _ := by ring
  let E := 5+5*D*(1+K)+3060*D*B
  have he : 0 ≤ E := by dsimp [E]; positivity
  have hbracket : 5*P*Real.sqrt P*M*Real.sqrt M+5*D*N^4*T*(N^2+H)*M+
        3060*D*N^7*T^3*(Real.log (2*N))^2 ≤ E*X*Z*V := by
    have h1 := mul_le_mul_of_nonneg_left (hv2.trans hvxz) (show (0:ℝ)≤5 by norm_num)
    have h2 := mul_le_mul_of_nonneg_left (hv3.trans hvz) (show 0 ≤ 5*D*(1+K)*X by positivity)
    have h3 := mul_le_mul_of_nonneg_left (hv1.trans hvx) (show 0 ≤ 3060*D*B*Z by positivity)
    have hh := add_le_add (add_le_add h1 (hm.trans h2)) (hb.trans h3)
    dsimp [E]
    convert hh using 1 <;> ring
  have hbase : 125*P^3+25*P^2*M ≤ 150*X*Y*Z*V := by
    have hvxyz : V ≤ X*Y*Z*V := by
      have hh := mul_le_mul_of_nonneg_right hY (show 0 ≤ X*Z*V by positivity)
      have hh' := hvxz.trans (by simpa only [one_mul] using hh)
      convert hh' using 1
      ring
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left (hv1.trans hvxyz) (show (0:ℝ)≤125 by norm_num))
      (mul_le_mul_of_nonneg_left (hv3.trans hvxyz) (show (0:ℝ)≤25 by norm_num))
    convert hh using 1 <;> ring
  have hprod : C*R*(5*P*Real.sqrt P*M*Real.sqrt M+5*D*N^4*T*(N^2+H)*M+
        3060*D*N^7*T^3*(Real.log (2*N))^2) ≤ C*(A*Y)*(E*X*Z*V) := by
    gcongr
  calc
    _ ≤ S*F*(125*P^3+C*R*(5*P*Real.sqrt P*M*Real.sqrt M+
        5*D*N^4*T*(N^2+H)*M+3060*D*N^7*T^3*(Real.log (2*N))^2)+25*P^2*M) := hraw
    _ ≤ S*F*(150*X*Y*Z*V+C*(A*Y)*(E*X*Z*V)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hS hF)
      linarith only [hbase,hprod]
    _ = _ := by dsimp [E,V]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.normalized_moment_absorption
#print axioms GuthMaynard.Improvement.normalized_moment_power_absorption
#print axioms GuthMaynard.Improvement.normalized_moment_uniform

#print axioms GuthMaynard.Improvement.raw_moment_normalized_budget
