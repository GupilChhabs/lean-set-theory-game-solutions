intro x h
rcases h with ha | hb
exact Or.inr ha
exact Or.inl hb
