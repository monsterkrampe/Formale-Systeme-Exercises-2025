-- This file is completely self contained. We even start with a basic Set definition.

def Set (α : Type u) := α -> Prop

-- The following type class instances are just allowing us to use some basic notation like ∅, ∈ or ∪ with the right definitions..
instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False

instance : Membership α (Set α) where
  mem S a := S a

instance : Union (Set α) where
  union A B := fun e => e ∈ A ∨ e ∈ B

instance : Inter (Set α) where
  inter A B := fun e => e ∈ A ∧ e ∈ B

instance : HasSubset (Set α) where
  Subset A B := ∀ e, e ∈ A -> e ∈ B

instance : HasSSubset (Set α) where
  SSubset A B := A ⊆ B ∧ ¬ B ⊆ A

-- Set extensionality: Two sets are equal if they contain the same elements. This is not something we define but we can prove it!
theorem Set.ext (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) -> X = Y := by
  intro h; apply funext; intro e; apply propext; specialize h e; exact h


-- Words are merely lists over some alphabet Sigma. In fact, we do not even care about the type of Sigma.
abbrev Word (Sigma : Type u) := List Sigma

-- A language is in turn just a set of words.
abbrev Language (Sigma : Type u) := Set (Word Sigma)

-- From now on, we pick some alphabet Sigma. In fact, we do not even care about the type of Sigma. In can basically be anything.
variable {Sigma : Type u}

-- Let's define concatenation as multiplication.
instance : Mul (Word Sigma) where
  mul u v := List.append u v

-- Also for Languages
instance : Mul (Language Sigma) where
  mul L1 L2 := fun w => ∃ u ∈ L1, ∃ v ∈ L2, w = u * v

-- For languages we can also execute concatenation multiple times and define this via Powers.
def Language.pow (L : Language Sigma) : Nat -> Language Sigma
| .zero => fun w => w = []
| .succ n => L * L.pow n

instance : NatPow (Language Sigma) where 
  pow L n := L.pow n 

-- Finally we define the Kleene Star and notation for it.
def Language.kstar (L : Language Sigma) : Language Sigma := fun w => ∃ n, w ∈ L^n
postfix:max "*" => Language.kstar

-- NOW FOR THE ACTUAL EXERCISE

section Exercise1

  variable {L1 L2 L3 L4 : Language Sigma}

  theorem a : L1 ⊆ L3 -> L2 ⊆ L4 -> L1 ∪ L2 ⊆ L3 ∪ L4 := by 
    -- First, we name both assumptions
    intro sub1 sub2 
    -- For any two sets A,B, A ⊆ B internally means ∀ w, w ∈ A -> w ∈ B.
    -- Therefore, we can fix an arbitrary w and name the assumption that w ∈ L1 ∪ L2
    intro w w_mem
    -- w ∈ L1 ∪ L2 internally unfolds to w ∈ L1 ∨ w ∈ L2. We can split those two cases.
    cases w_mem with 
    | inl w_mem => 
      -- When w ∈ L1, we want to prove that w ∈ L3 to conclude the proof.
      apply Or.inl
      -- According to sub1, w ∈ L3 follows if w ∈ L1.
      apply sub1
      -- Now, we just need to show w ∈ L1 but this is exactly our assumption w_mem.
      exact w_mem
    | inr w_mem => 
      -- Similar to the previous case
      apply Or.inr; apply sub2; exact w_mem

  theorem b : L1 ⊆ L3 -> L2 ⊆ L4 -> L1 * L2 ⊆ L3 * L4 := by 
    intro sub1 sub2 w w_mem
    -- L1 * L2 internally unfolds to ∃ u ∈ L1, ∃ v ∈ L2, w = u * v
    -- We can therefore introduce suitable u and v with the respective properties.
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    -- To show w ∈ L3 * L4, we need to show ∃ u ∈ L3, ∃ v ∈ L4, w = u * v
    -- But here, we can just pick the u and v that we already have.
    -- First, we pick u
    exists u
    -- We unfold the ∧ by its constructor, introducing 2 goals. One for each conjunct.
    constructor 
    -- We conclude the first goal, u ∈ L3 by using sub1 and the fact that u ∈ L1 holds.
    . exact sub1 _ u_mem
    -- Now we do the same for v.
    exists v
    constructor 
    . exact sub2 _ v_mem
    -- In the end, we still need to show that w = u * v but we already know that by w_eq.
    . exact w_eq

  theorem c : L1 ⊆ L3 -> L1* ⊆ L3* := by 
    intro sub w w_mem
    -- In general it might be helpful to unfold definitions manually to see what is underneath.
    unfold Language.kstar at w_mem
    rcases w_mem with ⟨n, w_mem⟩
    exists n

    -- We show something more general now. 
    have general_claim : ∀ n, L1^n ⊆ L3^n := by 
      intro n
      -- We can do this by induction over n.
      induction n with 
      | zero => 
        -- The base case is simple since L1 ^ 0 is definitionally equal to L3 ^ 0 and Lean knows that.
        intro w w_mem; exact w_mem
      | succ n ih =>
        intro w w_mem
        -- The definition of Language.pow is also inductive and we just unfold its inductive step here,
        -- which is defined as L ^ (n+1) = L * L^n. Therefore, this just works like concatenation.
        rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
        exists u
        constructor 
        . apply sub; exact u_mem
        exists v 
        constructor
        -- Here it gets interesting again. 
        -- To show v ∈ L3^n from v ∈ L1^n, we invoke the induction hypothesis that we named ih.
        . apply ih; exact v_mem
        . exact w_eq
    
    apply general_claim 
    exact w_mem

end Exercise1

section Exercise2 

  theorem a1 {L1 L2 L3 : Language Sigma} : L1 * (L2 ∪ L3) = L1 * L2 ∪ L1 * L3 := by 
    apply Set.ext
    intro w
    -- We can use the constructor tactic to split the ↔ into both -> directions.
    -- The rest should be similar to things seen above.
    constructor
    . intro w_mem
      rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
      cases v_mem with 
      | inl v_mem => 
        apply Or.inl
        exists u
        constructor 
        . exact u_mem
        exists v 
      | inr v_mem => 
        apply Or.inr
        exists u
        constructor 
        . exact u_mem
        exists v 
    . intro w_mem
      cases w_mem with 
      | inl w_mem => 
        rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
        exists u 
        constructor 
        . exact u_mem 
        exists v 
        constructor 
        . apply Or.inl; exact v_mem
        . exact w_eq
      | inr w_mem => 
        rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
        exists u 
        constructor 
        . exact u_mem 
        exists v 
        constructor 
        . apply Or.inr; exact v_mem
        . exact w_eq

  section a2 

    -- This whole thing is cumbersome since we really need to prove things about specific languages here.
    -- It's a bit ugly but it works.

    def L1 : Language Char := fun w => w = ['a'] ∨ w = ['a','b']
    def L2 : Language Char := fun w => w = ['c']
    def L3 : Language Char := fun w => w = ['b', 'c']

    theorem a2 : L1 * (L2 ∩ L3) ≠ (L1 * L2) ∩ (L1 * L3) := by 
      let prob_word := ['a', 'b', 'c']

      -- We show that we word abc is not in L1 * (L2 ∩ L3). Essentially this holds since L2 ∩ L3 is empty.
      have n_mem : prob_word ∉ L1 * (L2 ∩ L3) := by 
        intro contra
        rcases contra with ⟨_, _, _, v_mem, _⟩
        simp only [Inter.inter, Membership.mem, L2, L3] at v_mem
        rcases v_mem with ⟨l, r⟩
        rw [l] at r 
        simp at r

      -- We also show that abc is contained in (L1 * L2) ∩ (L1 * L3).
      have mem : prob_word ∈ (L1 * L2) ∩ (L1 * L3) := by 
        constructor
        . exists ['a', 'b']; simp [Membership.mem, L1]; exists ['c']
        . exists ['a']; simp [Membership.mem, L1]; exists ['b', 'c']

      -- Together, n_mem and mem contradict the supposed equality.
      intro contra
      apply n_mem
      rw [contra]
      exact mem

  end a2

  -- If you are up for a challenge, you can try to formalize and solve the remainder of Exercise 2.

end Exercise2

