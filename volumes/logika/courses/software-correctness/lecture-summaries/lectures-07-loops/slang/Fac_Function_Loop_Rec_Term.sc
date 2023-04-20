// #Sireum #Logika
import org.sireum._

// Definition by cases, equational
// Specification of the factorial function

@strictpure def fac_rec_spec(n: Z): Z = n match {
  case 0 => 1
  case m => m * fac_rec_spec(m - 1)
}

// Exercise: Prove termination of both factorial function implementations

@pure def fac_rec_term(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fac_rec_spec(n))
  )
  // decreases n
  val measure_n_entry = n
  Deduce(|- (measure_n_entry >= 0))
  if (n == 0) {
    return 1
  } else {
    val measure_n_call = n - 1
    Deduce(|- (measure_n_call < measure_n_entry))
    return n * fac_rec_term(n - 1)
  }
}

@pure def fac_it_term(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fac_rec_term(n))
  )
  var x: Z = 1
  var m: Z = 0;
  while (m < n) {
    // decreases n - m
    Invariant(
      Modifies(x, m),
      (x == fac_rec_term(m)),
      (m <= n),
      (m >= 0)
    )
    val measure_n_m_pre = n - m
    Deduce(|- (measure_n_m_pre >= 0))
    m = m + 1
    Deduce(|- (m >= 0))
    x = x * m
    val measure_n_m_post = n - m
    Deduce(|- (measure_n_m_post < measure_n_m_pre))
  }
  Deduce(|- (n == m))
  return x
}
