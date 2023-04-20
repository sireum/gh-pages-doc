// #Sireum #Logika
import org.sireum._

  
  // mathematically oriented specification of the factorial function
  @strictpure def fac_rec_spec(n: Z): Z = n match {
    case 0 => 1
    case m => m * fac_rec_spec(m - 1)
  }

  // recursive implementation of the factorial function
  @pure def fac_rec(n: Z): Z = {
    // no contract: we will instead verify/test using a refinement approach
    if (n == 0) {
      return 1
    } else {
      return n * fac_rec(n - 1)
    }
  }

  // iterative/imperative implementation of the factorial function
  @pure def fac_it(n: Z): Z = {
    // no contract: we will instead verify/test using a refinement approach
    var x: Z = 1
    var m: Z = 0;
    while (m < n) {
      m = m + 1
      x = x * m
    }
    return x
  }

  // Refinement specification:
  //  For all n >= Z,
  //   fac_it(n) refines (conforms to) fac_rec_spec(n)
  //  i.e.,
  //    fac_it(n) == fac_rec_spec(n)
  @pure def fac_imp_spec_refinement(n: Z) {
    Contract(
      Requires(n >= 0)
    )
    assert(fac_it(n) == fac_rec_spec(n))
  }

  // Refinement specification:
  //  For all n >= Z,
  //   fac_it(n) refines (conforms to) fac_rec(n)
  //  i.e.,
  //    fac_it(n) == fac_rec(n)
  @pure def fac_imp_rec_refinement(n: Z) {
    Contract(
      Requires(n >= 0)
    )
    assert(fac_it(n) == fac_rec(n))
  }

  // Refinement specification:
  //  For all n >= Z,
  //   fac_rec(n) refines (conforms to) fac_rec_spec(n)
  //  i.e.,
  //    fac_it(n) == fac_rec(n)
  @pure def fac_rec_spec_refinement(n: Z) {
    Contract(
      Requires(n >= 0)
    )
    assert(fac_rec(n) == fac_rec_spec(n))
  }


