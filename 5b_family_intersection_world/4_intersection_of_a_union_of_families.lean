ext x
apply Iff.intro
intro h
rw [mem_sInter] at h
constructor
rw [mem_sInter]
intro t h1
apply h t
left
exact h1
rw [mem_sInter]
intro t h1
apply h t
right
exact h1
intro h
rw [mem_sInter]
intro t h1
rcases h1 with h1a|h1b
exact h.left t h1a
exact h.right t h1b
