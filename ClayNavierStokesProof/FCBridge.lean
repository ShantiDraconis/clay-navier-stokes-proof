import ClayNavierStokes
import ClayNavierStokesProof.FCStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Dicionário: objetos fixados ⟷ objetos do Formal Conjectures

O enunciado fixado (`ClayNavierStokes`) usa derivadas `fderivWithin` no semiespaço
`H = ℝ³ × [0,∞)` (`dx`, `dt`, `lap`, `convect`, `grad`, `divx`), funções em `E3 × ℝ`, decaimento
com expoentes naturais e energia como integral de Lebesgue em `[0,∞]`. O Formal Conjectures
(`ClayNavierStokesProof.FC`) usa `fderiv` das fatias, `derivWithin` em `[0,∞)`, `Δ` e `gradient`
da Mathlib, divergência como traço, funções curryficadas `ℝ³ → ℝ → ℝ³`, decaimento com expoente
real e energia `MemLp _ 2 ∧ ∫ < E`.

Provado aqui, sem hipóteses:

* §1 nas fatias de funções lisas em `H`, cada operador fixado é o da Mathlib
  (`dx_eq`, `dt_eq`, `lap_eq`, `grad_eq`, `convect_eq`, `divx_eq`);
* §2 `smoothDivFree_decay4_iff`: `SmoothDivFree u₀ ∧ Decay4 u₀ ↔ InitialVelocityConditionDecay u₀`;
* §3 `forcing5_iff`: `Forcing5 f ↔ ForceConditionDecay (fun x t => f (x, t))`;
* §4 `goodSolutionR3_iff`: `GoodSolutionR3 ν u₀ f p u ↔`
  `NavierStokesExistenceAndSmoothnessRn ν u₀ (curry f) (curry u) (curry p)`.

Origem: a direção "FC ⇒ fixado" foi escrita numa auditoria anterior (arquivo de rascunho
`audit/ns/lean/Bridge.lean`); os lemas de fatia e de operadores seguem
`ATK/IntegracaoFCNS.lean` §1–2 (kernel ATK, espelho público `atk-math-core-public` @ `ffc111a`),
reescritos para os operadores do enunciado fixado. A direção "fixado ⇒ FC" das condições e a
volta da energia são novas.

Nada aqui resolve Navier–Stokes: `OPEN_MATH = true`.
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace ClayNavierStokesProof

open ClayNavierStokes

/-! ## 1. Operadores -/

/-- Expansão na base canônica: `∑ⱼ wⱼ eⱼ = w`. -/
theorem sum_coord (w : E3) : ∑ j, w j • e j = w := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  simpa [e] using this

/-- Traço em coordenadas: `tr A = ∑ⱼ (A eⱼ)ⱼ`. -/
theorem trace_eq_sum (A : E3 →L[ℝ] E3) :
    LinearMap.trace ℝ E3 (A : E3 →ₗ[ℝ] E3) = ∑ j, A (e j) j := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, e]

/-- A divergência do Formal Conjectures, em coordenadas. -/
theorem fc_divergence_eq_sum (v : E3 → E3) (x : E3) :
    FC.divergence v x = ∑ j, fderiv ℝ v x (e j) j := by
  rw [FC.divergence, trace_eq_sum]

/-- `H` tem diferenciação única (é convexo com interior não vazio). -/
theorem uniqueDiffOn_H : UniqueDiffOn ℝ H := uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fatia espacial `y ↦ g (y, t)` (com `t ≥ 0`) de uma função lisa em `H` tem como derivada a
derivada em `H` restrita a `ℝ³`. -/
theorem hasFDerivAt_slice {g : E3 × ℝ → F} (hg : ContDiffOn ℝ ∞ g H) {t : ℝ} (ht : 0 ≤ t)
    (x : E3) :
    HasFDerivAt (fun y => g (y, t))
      ((fderivWithin ℝ g H (x, t)).comp (ContinuousLinearMap.inl ℝ E3 ℝ)) x := by
  have hd : DifferentiableWithinAt ℝ g H (x, t) :=
    hg.differentiableOn (by simp) (x, t) ⟨mem_univ _, ht⟩
  have hi : HasFDerivAt (fun y : E3 => (y, t)) (ContinuousLinearMap.inl ℝ E3 ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact hasFDerivWithinAt_univ.mp
    (hd.hasFDerivWithinAt.comp x hi.hasFDerivWithinAt
      (fun y _ => (Set.mk_mem_prod (mem_univ y) ht : ((y, t) : E3 × ℝ) ∈ H)))

/-- `∂/∂x_j` fixado = derivada da fatia na direção `e_j`. -/
theorem dx_eq {g : E3 × ℝ → F} (hg : ContDiffOn ℝ ∞ g H) {t : ℝ} (ht : 0 ≤ t) (j : Fin 3)
    (x : E3) : dx j g (x, t) = fderiv ℝ (fun y => g (y, t)) x (e j) := by
  rw [(hasFDerivAt_slice hg ht x).fderiv]
  rfl

/-- `∂/∂t` fixado = derivada lateral `derivWithin` em `[0,∞)`. -/
theorem dt_eq {g : E3 × ℝ → F} (hg : ContDiffOn ℝ ∞ g H) {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    dt g (x, t) = derivWithin (fun s => g (x, s)) (Ici 0) t := by
  have hd : DifferentiableWithinAt ℝ g H (x, t) :=
    hg.differentiableOn (by simp) (x, t) ⟨mem_univ _, ht⟩
  have hc : HasDerivWithinAt (fun s : ℝ => ((x, s) : E3 × ℝ)) ((0 : E3), (1 : ℝ)) (Ici 0) t :=
    (hasDerivWithinAt_const t (Ici 0) x).prodMk (hasDerivWithinAt_id t (Ici 0))
  have h := hd.hasFDerivWithinAt.comp_hasDerivWithinAt (x := t) hc
    (fun s hs => (⟨mem_univ _, hs⟩ : ((x, s) : E3 × ℝ) ∈ H))
  have h' : HasDerivWithinAt (fun s => g (x, s)) ((fderivWithin ℝ g H (x, t)) (0, 1)) (Ici 0) t :=
    h
  rw [h'.derivWithin ((uniqueDiffOn_Ici 0) t ht)]
  rfl

/-- Fatias espaciais de funções lisas em `H` são lisas. -/
theorem slice_contDiff {g : E3 × ℝ → F} (hg : ContDiffOn ℝ ∞ g H) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun y => g (y, t)) := by
  rw [← contDiffOn_univ]
  exact hg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y _ => ⟨mem_univ _, ht⟩)

/-- `∂/∂x_j` preserva a suavidade em `H`. -/
theorem dx_contDiffOn {g : E3 × ℝ → F} (hg : ContDiffOn ℝ ∞ g H) (j : Fin 3) :
    ContDiffOn ℝ ∞ (dx j g) H := by
  have h : ContDiffOn ℝ ∞ (fderivWithin ℝ g H) H := hg.fderivWithin uniqueDiffOn_H (by simp)
  exact h.clm_apply contDiffOn_const

/-- Laplaciano fixado = laplaciano da Mathlib da fatia. -/
theorem lap_eq {u : E3 × ℝ → E3} (hu : ContDiffOn ℝ ∞ u H) {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    lap u (x, t) = Δ (fun y => u (y, t)) x := by
  have hs := slice_contDiff hu ht
  have h1 : ∀ j, dx j (dx j u) (x, t) =
      fderiv ℝ (fun y => fderiv ℝ (fun y' => u (y', t)) y (e j)) x (e j) := by
    intro j
    rw [dx_eq (dx_contDiffOn hu j) ht j x]
    congr 2
    funext y
    exact dx_eq hu ht j y
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply]
  unfold lap
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1 j]
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => u (y, t))) x :=
    ((hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp [e]

/-- Gradiente fixado = `gradient` da Mathlib da fatia. -/
theorem grad_eq {p : E3 × ℝ → ℝ} (hp : ContDiffOn ℝ ∞ p H) {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    grad p (x, t) = gradient (fun y => p (y, t)) x := by
  have h : ∀ j, (gradient (fun y => p (y, t)) x) j = fderiv ℝ (fun y => p (y, t)) x (e j) := by
    intro j
    have := EuclideanSpace.inner_single_left j (1 : ℝ) (gradient (fun y => p (y, t)) x)
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply] at this
    simpa [gradient, e] using this.symm
  rw [grad, ← sum_coord (gradient (fun y => p (y, t)) x)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dx_eq hp ht j x, h j]

/-- Termo convectivo fixado = `D(u(·,t))(x) (u(x,t))`. -/
theorem convect_eq {u : E3 × ℝ → E3} (hu : ContDiffOn ℝ ∞ u H) {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    convect u (x, t) = fderiv ℝ (fun y => u (y, t)) x (u (x, t)) := by
  conv_rhs => rw [← sum_coord (u (x, t))]
  rw [map_sum]
  unfold convect
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, dx_eq hu ht j x]

/-- Divergência fixada = divergência (traço) do Formal Conjectures da fatia. -/
theorem divx_eq {u : E3 × ℝ → E3} (hu : ContDiffOn ℝ ∞ u H) {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    divx u (x, t) = FC.divergence (fun y => u (y, t)) x := by
  rw [fc_divergence_eq_sum]
  unfold divx
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dx_eq hu ht j x]

/-! ## 2. Decaimento: expoentes naturais ⟷ expoentes reais -/

/-- De `a^⌈K⌉₊ · b ≤ C` (com `a ≥ 1`, `b ≥ 0`) segue `b ≤ C / a^K` para o expoente real `K`. -/
theorem le_div_rpow_of_mul_le {a b C : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (K : ℝ)
    (h : a ^ ⌈K⌉₊ * b ≤ C) : b ≤ C / a ^ K := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hC : 0 ≤ C := le_trans (mul_nonneg (pow_nonneg ha0.le _) hb) h
  have h1 : a ^ K ≤ a ^ (⌈K⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le ha (Nat.le_ceil K)
  rw [Real.rpow_natCast] at h1
  calc b ≤ C / a ^ ⌈K⌉₊ := by
        rw [le_div_iff₀ (pow_pos ha0 _), mul_comm]; exact h
    _ ≤ C / a ^ K := div_le_div_of_nonneg_left hC (Real.rpow_pos_of_pos ha0 K) h1

/-- De `b ≤ C / a^(K : ℝ)` (com `a > 0`, `K : ℕ`) segue `a^K · b ≤ C`. -/
theorem mul_le_of_le_div_rpow {a b C : ℝ} (ha : 0 < a) (K : ℕ)
    (h : b ≤ C / a ^ (K : ℝ)) : a ^ K * b ≤ C := by
  rw [Real.rpow_natCast, le_div_iff₀ (pow_pos ha K)] at h
  linarith [mul_comm (a ^ K) b]

/-- **Dado inicial**: as hipóteses fixadas `SmoothDivFree ∧ Decay4` são exatamente
`InitialVelocityConditionDecay` do Formal Conjectures. -/
theorem smoothDivFree_decay4_iff (u₀ : E3 → E3) :
    SmoothDivFree u₀ ∧ Decay4 u₀ ↔ FC.InitialVelocityConditionDecay u₀ := by
  constructor
  · rintro ⟨⟨hs, hdiv⟩, hdec⟩
    refine { div_free := fun x => ?_, smooth := hs, decay := fun m K => ?_ }
    · rw [fc_divergence_eq_sum]; exact hdiv x
    · obtain ⟨C, hC⟩ := hdec m ⌈K⌉₊
      exact ⟨C, fun x => le_div_rpow_of_mul_le (by linarith [norm_nonneg x]) (norm_nonneg _) K
        (hC x)⟩
  · intro h
    refine ⟨⟨h.smooth, fun x => ?_⟩, fun k K => ?_⟩
    · rw [← fc_divergence_eq_sum]; exact h.div_free x
    · obtain ⟨C, hC⟩ := h.decay k K
      exact ⟨C, fun x => mul_le_of_le_div_rpow (by positivity) K (hC x)⟩

/-! ## 3. Força -/

/-- **Força**: a hipótese fixada `Forcing5 f` (em `ℝ³ × [0,∞)`) é exatamente
`ForceConditionDecay` do Formal Conjectures para a forma curryficada de `f`. -/
theorem forcing5_iff (f : E3 × ℝ → E3) :
    Forcing5 f ↔ FC.ForceConditionDecay (fun x t => f (x, t)) := by
  constructor
  · rintro ⟨hs, hdec⟩
    refine { smooth := hs, decay := fun m K => ?_ }
    obtain ⟨C, hC⟩ := hdec m ⌈K⌉₊
    refine ⟨C, fun x t ht => ?_⟩
    have hz : ((x, t) : E3 × ℝ) ∈ H := ⟨mem_univ _, ht⟩
    exact le_div_rpow_of_mul_le (by linarith [norm_nonneg x]) (norm_nonneg _) K (hC (x, t) hz)
  · intro h
    refine ⟨h.smooth, fun k K => ?_⟩
    obtain ⟨C, hC⟩ := h.decay k K
    refine ⟨C, fun z hz => ?_⟩
    have hz2 : (0 : ℝ) ≤ z.2 := hz.2
    have hpos : (0 : ℝ) < 1 + ‖z.1‖ + z.2 := by positivity
    exact mul_le_of_le_div_rpow hpos K (hC z.1 z.2 hz2)

/-! ## 4. Soluções em `ℝ³` -/

/-- Uma solução no sentido fixado é uma solução do Formal Conjectures (formas curryficadas). -/
theorem fcSolution_of_goodSolutionR3 {ν : ℝ} {u₀ : E3 → E3} {f : E3 × ℝ → E3}
    {p : E3 × ℝ → ℝ} {u : E3 × ℝ → E3} (h : GoodSolutionR3 ν u₀ f p u) :
    FC.NavierStokesExistenceAndSmoothnessRn ν u₀ (fun x t => f (x, t)) (fun x t => u (x, t))
      (fun x t => p (x, t)) := by
  obtain ⟨hsol, ⟨hp, hu⟩, ⟨C, hC⟩⟩ := h
  have hcont : ∀ t, 0 ≤ t → Continuous (fun x => u (x, t)) := fun t ht =>
    (slice_contDiff hu ht).continuous
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x t ht
    have hm := hsol.momentum (x, t) ⟨mem_univ _, ht⟩
    rw [dt_eq hu ht, convect_eq hu ht, lap_eq hu ht, grad_eq hp ht] at hm
    exact hm
  · intro x t ht
    rw [← divx_eq hu ht]
    exact hsol.incompressible (x, t) ⟨mem_univ _, ht⟩
  · intro x
    exact hsol.initial x
  · exact hu
  · exact hp
  · intro t ht
    have hm : AEStronglyMeasurable (fun x => ‖u (x, t)‖) volume :=
      (continuous_norm.comp (hcont t ht)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hm]
    refine ⟨(((continuous_norm.comp (hcont t ht)).norm).pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)]
    simp only [norm_norm]
    exact lt_of_le_of_lt (hC t ht) ENNReal.ofReal_lt_top
  · refine ⟨max C 0 + 1, fun t ht => ?_⟩
    have hm2 : AEStronglyMeasurable (fun x => ‖u (x, t)‖ ^ 2) volume :=
      ((continuous_norm.comp (hcont t ht)).pow 2).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (show (0 : ℝ) ≤ ‖u (x, t)‖ ^ 2 from sq_nonneg _)) hm2]
    have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC t ht)
    rw [ENNReal.toReal_ofReal'] at h3
    linarith

/-- Uma solução do Formal Conjectures é uma solução no sentido fixado. -/
theorem goodSolutionR3_of_fcSolution {ν : ℝ} {u₀ : E3 → E3} {f : E3 × ℝ → E3}
    {p : E3 × ℝ → ℝ} {u : E3 × ℝ → E3}
    (h : FC.NavierStokesExistenceAndSmoothnessRn ν u₀ (fun x t => f (x, t))
      (fun x t => u (x, t)) (fun x t => p (x, t))) :
    GoodSolutionR3 ν u₀ f p u := by
  have hu : ContDiffOn ℝ ∞ u H := h.velocity_smooth
  have hp : ContDiffOn ℝ ∞ p H := h.pressure_smooth
  refine ⟨⟨fun z hz => ?_, fun z hz => ?_, fun x => h.initial_condition x⟩, ⟨hp, hu⟩, ?_⟩
  · obtain ⟨x, t⟩ := z
    have ht : 0 ≤ t := hz.2
    rw [dt_eq hu ht, convect_eq hu ht, lap_eq hu ht, grad_eq hp ht]
    exact h.navier_stokes x t ht
  · obtain ⟨x, t⟩ := z
    have ht : 0 ≤ t := hz.2
    rw [divx_eq hu ht]
    exact h.div_free x t ht
  · obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨E, fun t ht => ?_⟩
    have hm : AEStronglyMeasurable (fun x => ‖u (x, t)‖) volume :=
      (continuous_norm.comp (slice_contDiff hu ht).continuous).aestronglyMeasurable
    have hint : Integrable (fun x => ‖u (x, t)‖ ^ 2) volume := by
      have := (memLp_two_iff_integrable_sq_norm hm).mp (h.integrable t ht)
      simpa only [norm_norm] using this
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hE t ht).le

/-- **Soluções**: `GoodSolutionR3` fixado ⟺ `NavierStokesExistenceAndSmoothnessRn` do Formal
Conjectures, para as formas curryficadas de `f`, `u`, `p`. -/
theorem goodSolutionR3_iff {ν : ℝ} {u₀ : E3 → E3} {f : E3 × ℝ → E3} {p : E3 × ℝ → ℝ}
    {u : E3 × ℝ → E3} :
    GoodSolutionR3 ν u₀ f p u ↔
      FC.NavierStokesExistenceAndSmoothnessRn ν u₀ (fun x t => f (x, t)) (fun x t => u (x, t))
        (fun x t => p (x, t)) :=
  ⟨fcSolution_of_goodSolutionR3, goodSolutionR3_of_fcSolution⟩

end ClayNavierStokesProof
