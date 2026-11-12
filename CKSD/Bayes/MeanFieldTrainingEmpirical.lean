module
public import CKSD.Bayes.MeanFieldTrainingParticles
/-!
# Almost-sure empirical training limits on all compact horizons

Iid initial states generate integrable characteristic paths on each compact
interval. Their empirical first-Wasserstein convergence and deterministic
particle coupling give uniform convergence of empirical marginals. A countable
intersection over integer horizons yields the conclusion simultaneously on
all bounded nonnegative time intervals, without particle measurability.

The local characteristic-path and synchronous-coupling adapters supply the
estimates; pinned TauCeti supplies empirical Wasserstein consistency. This is
the empirical conclusion of the mean-field neural-network limit, GAPS 104.53.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology
namespace CKSD
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- Iid initial states and bounded-speed characteristic paths give uniform empirical
mean-field convergence on each fixed compact interval. -/
theorem ae_tendsto_iSup_empirical_training_laws_on_Icc
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ₀ : Measure E)
    (hρ : Integrable (fun x : E ↦ ‖x‖) ρ₀)
    (ξ : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed P ξ ρ₀)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (γ : E → ℝ → E) (hγ : Continuous (uncurry γ)) (hzero : ∀ x, γ x 0=x)
    {M : ℝ≥0} (hγL : ∀ x, LipschitzWith M (γ x))
    (v : ℝ × E → E) (hv : Continuous v)
    (hd : ∀ x t, HasDerivAt (γ x) (v (t,γ x t)) t)
    (hvEq : ∀ t ≥ 0, ∀ x, v (t,x)=b x (ρ₀.map (fun y ↦ γ y t)))
    (θ : ℕ → ℕ → ℝ → Ω → E)
    (hθ : ∀ N, ∀ i<N, ∀ ω, θ N i 0 ω=ξ i ω ∧ ∀ t, HasDerivAt (fun s ↦ θ N i s ω)
      (b (θ N i t ω) (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω))) t)
    {T : ℝ} (hT : 0≤T) :
    ∀ᵐ ω ∂P, Tendsto (fun N ↦ ⨆ t∈Icc (0:ℝ) T, TauCeti.wassersteinEDist 1
      (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω)) (ρ₀.map (fun y ↦ γ y t))) atTop (𝓝 0) := by
  obtain ⟨Z,hZdef,hZm,hZi,hind,hid,hZmap,hZeval⟩ :=
    exists_iid_training_paths_on_Icc P ρ₀ hρ ξ hiid.1 hiid.2.1 hiid.2.2 hT γ hγ hγL hzero
  have hZe (i : ℕ) (ω : Ω) (t : Icc (0:ℝ) T) : Z i ω t = ξ i ω + ∫ s in (0:ℝ)..t,
      b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s)) := by
    have h := training_path_integral_eq P ρ₀ ξ hT γ v hv hd hzero b hvEq Z hZeval
      (fun t ht ↦ hZmap 0 t ht) i ω t t.2
    have hzt : (Z i ω).IccExtend hT t = Z i ω t :=
      Set.IccExtend_of_mem (h := hT) (fun u ↦ Z i ω u) t.2
    rwa [hzt] at h
  filter_upwards [ae_tendsto_iSup_empirical_particle_marginals P hT b hb Z hZm (hZi 0)
    hind hid ξ hZe θ hθ] with ω hω
  convert hω using 1
  funext N
  apply iSup_congr
  intro t
  apply iSup_congr
  intro ht
  rw [hZmap 0 t ht]
/-- A countable family of compact-horizon estimates gives almost-sure uniform empirical
convergence on every bounded nonnegative time interval, without particle measurability. -/
theorem ae_tendsto_iSup_empirical_training_laws
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ₀ : Measure E)
    (hρ : Integrable (fun x : E ↦ ‖x‖) ρ₀)
    (ξ : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed P ξ ρ₀)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (γ : E → ℝ → E) (hγ : Continuous (uncurry γ)) (hzero : ∀ x, γ x 0=x)
    {M : ℝ≥0} (hγL : ∀ x, LipschitzWith M (γ x))
    (v : ℝ × E → E) (hv : Continuous v)
    (hd : ∀ x t, HasDerivAt (γ x) (v (t,γ x t)) t)
    (hvEq : ∀ t ≥ 0, ∀ x, v (t,x)=b x (ρ₀.map (fun y ↦ γ y t)))
    (θ : ℕ → ℕ → ℝ → Ω → E)
    (hθ : ∀ N, ∀ i<N, ∀ ω, θ N i 0 ω=ξ i ω ∧ ∀ t, HasDerivAt (fun s ↦ θ N i s ω)
      (b (θ N i t ω) (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω))) t) :
    ∀ᵐ ω ∂P, ∀ T>0, Tendsto (fun N ↦ ⨆ t∈Icc (0:ℝ) T, TauCeti.wassersteinEDist 1
      (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω)) (ρ₀.map (fun y ↦ γ y t))) atTop (𝓝 0) := by
  have hall (n : ℕ) : ∀ᵐ ω ∂P, Tendsto (fun N ↦ ⨆ t∈Icc (0:ℝ) ((n:ℝ)+1),
      TauCeti.wassersteinEDist 1 (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω))
        (ρ₀.map (fun y ↦ γ y t))) atTop (𝓝 0) :=
    ae_tendsto_iSup_empirical_training_laws_on_Icc P ρ₀ hρ ξ hiid b hb γ hγ hzero hγL
      v hv hd hvEq θ hθ (by positivity)
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  intro T hT
  obtain ⟨n,hn⟩ := exists_nat_ge T
  have hTn : T ≤ (n:ℝ)+1 := by linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hω n) (fun _ ↦ zero_le)
  intro N
  apply iSup₂_le
  intro t ht
  exact le_iSup_of_le t (le_iSup_of_le (⟨ht.1,ht.2.trans hTn⟩ : t∈Icc (0:ℝ) ((n:ℝ)+1)) le_rfl)
end CKSD
