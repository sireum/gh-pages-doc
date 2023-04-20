// #Sireum #Logika
import org.sireum._

// What happens if this is called with k == -1?
// Divergence
// Add measure to show that the function terminates for all parameters
// that satisfy the precondition.
// Measure: m (on well-founded set {x | x >= 0}
// m decreases in each iteration of the loop
@pure def while0_div(k: Z): Z = {
  Contract(

    Ensures(Res == 0)
  )
  var m: Z = k
  while (m != 0) {
    // decreases m
    val measure_m_pre = m
    Deduce(|- (measure_m_pre >= 0))
    m = m - 1
    val measure_m_post = m
    Deduce(|- (measure_m_post < measure_m_pre))
  }
  return 0
}

// What happens if this is called with k == -1?
// Divergence
// Add measure to show that the function terminates for all parameters
// that satisfy the precondition.
// Measure: k (on well-founded set {x | x >= 0}
// k decreases with each recursive call
@pure def count0(k: Z): Z = {
  Contract(

    Ensures(Res == 0)
  )
  // decreases k
  val measure_k_entry: Z = k
  Deduce(|- (k >= 0))
  if (k == 0) {
    return k
  } else {
    val measure_k_call: Z = k - 1
    Deduce(|- (measure_k_call < measure_k_entry))
    return count0(k - 1)
  }
}