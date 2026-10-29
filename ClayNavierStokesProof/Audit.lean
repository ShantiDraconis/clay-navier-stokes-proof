import ClayNavierStokesProof.FCStatements
import ClayNavierStokesProof.FCBridge
import ClayNavierStokesProof.FCClay

/-!
# Auditoria de axiomas

Cada `#guard_msgs` fixa a saída real de `#print axioms`. Se aparecer qualquer axioma diferente
(inclusive `sorryAx`), a compilação falha. Só aparecem `propext`, `Classical.choice` e
`Quot.sound`; `Classical.choice` já vem de `ℝ` na Mathlib (`#print axioms Real`).

Nenhuma declaração deste repositório usa `axiom`: o resultado externo da OpenAI entra apenas
como a `Prop` nomeada `FCBreakdownR3`, hipótese de `clayC_of_fcBreakdown`.
-/

/-- info: 'ClayNavierStokesProof.FC.divergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FC.divergence

/-- info: 'ClayNavierStokesProof.FC.InitialVelocityCondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FC.InitialVelocityCondition

/-- info: 'ClayNavierStokesProof.FC.InitialVelocityConditionDecay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FC.InitialVelocityConditionDecay

/-- info: 'ClayNavierStokesProof.FC.ForceCondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FC.ForceCondition

/-- info: 'ClayNavierStokesProof.FC.ForceConditionDecay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FC.ForceConditionDecay

/-- info: 'ClayNavierStokesProof.FC.NavierStokesExistenceAndSmoothness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FC.NavierStokesExistenceAndSmoothness

/-- info: 'ClayNavierStokesProof.FC.NavierStokesExistenceAndSmoothnessRn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FC.NavierStokesExistenceAndSmoothnessRn

/-- info: 'ClayNavierStokesProof.FCExistenceR3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FCExistenceR3

/-- info: 'ClayNavierStokesProof.FCBreakdownR3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.FCBreakdownR3

/-- info: 'ClayNavierStokesProof.sum_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.sum_coord

/-- info: 'ClayNavierStokesProof.trace_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.trace_eq_sum

/-- info: 'ClayNavierStokesProof.fc_divergence_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.fc_divergence_eq_sum

/-- info: 'ClayNavierStokesProof.uniqueDiffOn_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.uniqueDiffOn_H

/-- info: 'ClayNavierStokesProof.hasFDerivAt_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.hasFDerivAt_slice

/-- info: 'ClayNavierStokesProof.dx_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.dx_eq

/-- info: 'ClayNavierStokesProof.dt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.dt_eq

/-- info: 'ClayNavierStokesProof.slice_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.slice_contDiff

/-- info: 'ClayNavierStokesProof.dx_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.dx_contDiffOn

/-- info: 'ClayNavierStokesProof.lap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.lap_eq

/-- info: 'ClayNavierStokesProof.grad_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.grad_eq

/-- info: 'ClayNavierStokesProof.convect_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.convect_eq

/-- info: 'ClayNavierStokesProof.divx_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.divx_eq

/-- info: 'ClayNavierStokesProof.le_div_rpow_of_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.le_div_rpow_of_mul_le

/-- info: 'ClayNavierStokesProof.mul_le_of_le_div_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.mul_le_of_le_div_rpow

/-- info: 'ClayNavierStokesProof.smoothDivFree_decay4_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.smoothDivFree_decay4_iff

/-- info: 'ClayNavierStokesProof.forcing5_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.forcing5_iff

/-- info: 'ClayNavierStokesProof.fcSolution_of_goodSolutionR3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.fcSolution_of_goodSolutionR3

/-- info: 'ClayNavierStokesProof.goodSolutionR3_of_fcSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.goodSolutionR3_of_fcSolution

/-- info: 'ClayNavierStokesProof.goodSolutionR3_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.goodSolutionR3_iff

/-- info: 'ClayNavierStokesProof.clayA_iff_fcExistenceR3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.clayA_iff_fcExistenceR3

/-- info: 'ClayNavierStokesProof.target_iff_fcExistenceR3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.target_iff_fcExistenceR3

/-- info: 'ClayNavierStokesProof.clayC_iff_fcBreakdownR3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.clayC_iff_fcBreakdownR3

/-- info: 'ClayNavierStokesProof.clayC_of_fcBreakdown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokesProof.clayC_of_fcBreakdown
