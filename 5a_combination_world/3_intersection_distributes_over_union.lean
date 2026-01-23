ext x
apply Iff.intro
intro h
have h1 : x ∈ B ∪ C := h.right
rcases h1 with h1a | h1b
left
constructor
exact h.left
exact h1a
right
constructor
exact h.left
exact h1b
intro h
rcases h with h1 | h2
constructor
exact h1.left
left
exact h1.right
constructor
exact h2.left
right
exact h2.right
