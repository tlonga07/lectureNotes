(   
   ∃((x: T) => (P(x) ∧ Q(x)))
) 
⊢  
(  ∃((x: T) => Q(x) )  )

Proof(
    1 ( ∃((x: T) => (P(x) ∧ Q(x))) ) by Premise,
    //type what would go here
    Proof
    2 Let((alias: T) => Subproof(
        3 Assume ( P(alias) & Q(alias) ),
        4 ( Q(alias) ) by AndE2(3),
        5 (∃((x: T) => Q(x)) ) by ExistsI[T](4)
    ))
    6 (∃((x: T) => Q(x)) by ExistsE(1, 2))

)