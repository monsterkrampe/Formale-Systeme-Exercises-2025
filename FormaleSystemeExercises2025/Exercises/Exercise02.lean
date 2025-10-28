import FormaleSystemeExercises2025.Exercises.Exercise01

-- inspired by mathlib
class Fintype (α : Type u) where 
  elems : List α
  complete : ∀ a : α, a ∈ elems


structure DFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → Option Q
  q0 : Q
  F : List Q

structure NFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → List Q
  Q0 : List Q
  F : List Q

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma]

def DFA.δ_word (dfa : DFA Q Sigma) (q : Q) : (Word Sigma) -> Option Q 
| .nil => .some q
| .cons a v => (dfa.δ q a).bind (fun q' => dfa.δ_word q' v)

def DFA.Language (dfa : DFA Q Sigma) : Language Sigma := 
  fun w => ∃ qf, dfa.δ_word dfa.q0 w = some qf ∧ qf ∈ dfa.F

inductive NFA.Run (nfa : NFA Q Sigma) : Q -> Q -> Word Sigma -> Type _
| self (q : Q) : nfa.Run q q []
| step {q1 q2 qf : Q} {a : Sigma} {v : Word Sigma} (r : nfa.Run q2 qf v) (q2_mem : q2 ∈ nfa.δ q1 a) : nfa.Run q1 qf (a :: v)

def NFA.Run.from_start {nfa : NFA Q Sigma} (_ : nfa.Run q0 q w) : Prop := q0 ∈ nfa.Q0
def NFA.Run.accepts {nfa : NFA Q Sigma} (_ : nfa.Run q qf w) : Prop := qf ∈ nfa.F

def NFA.Language (nfa : NFA Q Sigma) : Language Sigma := 
  fun w => ∃ (q0 qf : Q) (r : nfa.Run q0 qf w), r.from_start ∧ r.accepts


section Exercise3

  variable {Q1 : Type u1} {Q2 : Type u2} [Fintype Q1] [Fintype Q2]

  structure NFASimulation (nfa1 : NFA Q1 Sigma) (nfa2 : NFA Q2 Sigma) where 
    rel : Set (Q1 × Q2)
    start : ∀ q01 ∈ nfa1.Q0, ∃ q02 ∈ nfa2.Q0, (q01, q02) ∈ rel
    step : ∀ {q1 : Q1} {q2 : Q2} {a : Sigma}, (q1, q2) ∈ rel -> ∀ q1' ∈ (nfa1.δ q1 a), ∃ q2' ∈ (nfa2.δ q2 a), (q1', q2') ∈ rel
    final : ∀ {q1 : Q1} {q2 : Q2}, (q1, q2) ∈ rel -> q1 ∈ nfa1.F -> q2 ∈ nfa2.F

  section d 
    
    theorem part_a {nfa1 : NFA Q1 Sigma} {nfa2 : NFA Q2 Sigma} (sim : NFASimulation nfa1 nfa2) : nfa1.Language ⊆ nfa2.Language := by 
      have generalized_theorem : ∀ {q1 q1' : Q1} {q2 : Q2} {w : Word Sigma}, (q1, q2) ∈ sim.rel -> ∀ r1 : nfa1.Run q1 q1' w, ∃ q2' : Q2, (q1', q2') ∈ sim.rel ∧ ∃ r2 : nfa2.Run q2 q2' w, True := by 
        intro q1 q1' q2 w q1_eq_q2 r1
        induction r1 generalizing q2 with 
        | self q => exists q2; constructor; exact q1_eq_q2; exists (.self q2)
        | step r1 q2_mem ih => 
          rcases sim.step q1_eq_q2 _ q2_mem with ⟨_, q2'_mem, q1'_eq_q2'⟩
          specialize ih q1'_eq_q2'
          rcases ih with ⟨q2'', q2''_eq, r2, _⟩
          exists q2''
          constructor 
          . exact q2''_eq
          . exists (.step r2 q2'_mem)

      intro w w_mem
      rcases w_mem with ⟨q01, qf1, r1, r1_start, r1_accept⟩
      rcases sim.start q01 r1_start with ⟨q02, r2_start, q01_eq_q02⟩
      exists q02
      rcases generalized_theorem q01_eq_q02 r1 with ⟨qf2, qf1_eq_qf2, r2, _⟩
      exists qf2, r2
      constructor 
      . exact r2_start
      . exact sim.final qf1_eq_qf2 r1_accept

  end d

end Exercise3

