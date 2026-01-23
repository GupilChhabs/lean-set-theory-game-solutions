ext x
apply Iff.intro
intro h
constructor
by_contra h1
rw [mem_compl_iff] at h1
push_neg at h1
rw [mem_compl_iff] at h
have h2 : x ∈ A ∪ B
left
exact h1
exact h h2
by_contra h1
rw [mem_compl_iff] at h1
push_neg at h1
rw [mem_compl_iff] at h
have h2:  x ∈ A ∪ B
right
exact h1
exact h h2
intro h
rw [mem_compl_iff]
by_contra h1
have h2 : x∈ A
rcases h1 with h1a | h1b
exact h1a
by_contra h2
exact h.right h1b
exact h.left h2
