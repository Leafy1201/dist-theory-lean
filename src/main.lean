import analysis.normed.field.basic
import analysis.normed.group.infinite_sum
import data.matrix.basic
import topology.sequences
import algebra.direct_sum.module
import analysis.complex.basic
import analysis.convex.uniform
import analysis.normed_space.bounded_linear_maps
import analysis.normed_space.banach
import linear_algebra.bilinear_form
import linear_algebra.sesquilinear_form



import algebra.module.pi
import topology.support
import analysis.calculus.cont_diff
import order.complete_lattice
import data.real.basic
import analysis.calculus.deriv
import analysis.calculus.iterated_deriv
import algebra.module.pi
import algebra.module.linear_map

noncomputable theory

def smooth (f:ℝ → ℝ) := ∀n:ℕ, cont_diff ℝ n f

def mem_test (f:ℝ → ℝ) : Prop := (has_compact_support f) ∧ (smooth f)

class test_function := 
mk :: (f : ℝ → ℝ) (test : mem_test f )

--def seminorm (f:ℝ→ℝ) [mem_test f] (n:ℕ) := Sup(f '' {x:ℝ | true})

notation f`#`n := iterated_deriv n f

def seminorm (f:ℝ→ℝ) (n:ℕ) := Sup((( abs (f#n)) '' {x:ℝ | true}))

notation `||`f`||_`n := seminorm f n



-- def d_convergence (u:ℕ→(ℝ→ℝ)) [hu : ∀n, mem_test (u n)]  (f:ℝ→ℝ)  [mem_test f] [hf : mem_test f]

--need to restrict to test functions only
def d_convergence (u:ℕ→(ℝ→ℝ)) (f:ℝ→ℝ): Prop :=
(∃ K, is_compact(K) ∧ (∀ n, tsupport (u n) ⊆ K) ∧ (tsupport f ⊆ K) ∧ (∀ n, tsupport (f - u n) ⊆ K) ∧ (∀ε>0,∀N:ℕ, ∃K:ℕ, ∀n, n≥K → (|| f - u n ||_N) ≤ ε))


--need to change to only restict as a functional on test functions maybe use submodule structure

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- change this so it depends on the mathlib version of limits and not the limit above
def is_distribution (u: (ℝ→ℝ) → ℝ) : Prop := 
(is_linear_map ℝ u) ∧ (∀ v:ℕ→(ℝ→ℝ), ∀f, d_convergence v f → seq_limit (u∘v) (u f))


lemma zero_mem_test : mem_test (λ x, 0) :=
begin
  let f := (λ (x : ℝ), 0),
  unfold mem_test,
  split,
  unfold has_compact_support,
  have F :  ∅ = function.support (λ (x : ℝ), 0),
    simp,
  unfold tsupport,
  have G : closure(function.support (λ (x : ℝ), 0)) = closure(∅),
    simp,
  simp,
  intro n,
  exact cont_diff_const,
end


lemma add_mem_test {f g : ℝ → ℝ} (hf : mem_test f) (hg : mem_test g) : mem_test (f+g)  := 
begin
  split,
  exact has_compact_support.add hf.1 hg.1,
  intro n,
  exact cont_diff.add (hf.2 n) (hg.2 n),
end

lemma mul_C_inf_right_mem_test  {f g : ℝ → ℝ} (hf : mem_test f) (hg : smooth g) : mem_test (f*g) :=
begin
  split,
  exact has_compact_support.mul_right hf.1,
  intro n,
  exact cont_diff.mul (hf.2 n) (hg n),
end

lemma mul_C_inf_left_mem_test  {f g : ℝ → ℝ} (hf : smooth f) (hg : mem_test g) : mem_test (f*g) :=
begin
  split,
  exact has_compact_support.mul_left hg.1,
  intro n,
  exact cont_diff.mul (hf n) (hg.2 n),
end

lemma mul_mem_test {f g : ℝ → ℝ} (hf : mem_test f) (hg : mem_test g) : mem_test (f*g) :=
begin
  exact mul_C_inf_left_mem_test hf.2 hg,
end

lemma smul_mem_test {c : ℝ} {g : ℝ → ℝ} (hg : mem_test g) : mem_test (c•g) :=
begin
  have : (c•g) = (λ (x : ℝ), c) * g,
    refl,

  rw this,
  have : smooth (λ (x : ℝ), c),
    intro n,
    exact cont_diff_const,

  exact mul_C_inf_left_mem_test this hg,
end

#check is_compact


theorem local_boundedness_principle (u: (ℝ→ℝ) → ℝ) (lin: is_linear_map ℝ u) :
is_distribution u ↔ (∀K:(set ℝ), is_compact(K) → ∃c≥0, ∃n:ℕ, ∀f, tsupport (f) ⊆ K → abs (u f) ≤ c*(finsum (λ k :fin(n+1), ||f||_k)))
:=
begin
  split,
  intros dist_prop,
  by_contra C,
  push_neg at C,
  cases C with K C,
  cases C with K_comp C,
  
  let G := λ n:ℕ, C n (by simp) n ,

  choose v hv1 hv2 using G,


  
  have zero := is_linear_map.map_zero dist_prop.1,

  --TODO, show that f n = (v n)/ (u v n) D-converges to 0, but u f n = 1 for every n
  sorry,

  intros bddness,
  split,
  exact lin,

  intros v f conv ε ε_pos,

  rcases conv with ⟨ K, comp_K, comp_v, comp_f, comp_fv, conv⟩,

  specialize bddness K comp_K,

  rcases bddness with ⟨ c, c_pos, N, bddness ⟩,


  have G1 : 0  < ε/((c+1)*(N+1)),
  --fix this
    sorry,
  

  specialize conv (ε/((c+1)*(N+1))) G1,

  -- choose conv, with j then take max of K_j from 0 to N+1, use max and then conclude by calc

  --specialize bddness (f - (v n)) (comp_fv n),
  



end

#eval 1+1