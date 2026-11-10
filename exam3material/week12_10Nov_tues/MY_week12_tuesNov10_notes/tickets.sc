// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//adult tickets: $50
//kid tickets: $30
def getTicketCosts(adult: Z, kid: Z): Z = {
  //what do we want for our function contract?
  Contract(
    Requires(adult >= 0, kid >= 0),
    Ensures(Res[Z] == adult*50 + kid*30, Res[Z] >= 0)
  )


  //what to do here?


  //get the total ticket cost
  val overall: Z = adult*50 + kid*30

  //what to do here?

  return overall
}

////////////// Test code /////////////////

val k: Z = 3 //$30 each
val a: Z = 2 //$50 each

//what to do here?
//prove preconditions (requires) abt parameters being passed

Deduce(
  1 ( a == 2 ) by Premise,
  2 ( k == 3 ) by Premise, 
  3 ( a >= 0 ) by Algbera*(1),
  4 ( k >= 0 ) by Algebra*(2), 
)
assert( a >= 0 )
assert( k >= 0 )
val cost: Z = getTicketCosts(a, k)

//what to do here?

//what *should* cost be?
assert(cost == 190)