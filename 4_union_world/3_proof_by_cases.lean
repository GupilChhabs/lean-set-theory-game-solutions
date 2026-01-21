intro x h3
rw [mem_union] at h3
rcases h3 with h3a | h3b
exact h1 h3a
exact h2 h3b
