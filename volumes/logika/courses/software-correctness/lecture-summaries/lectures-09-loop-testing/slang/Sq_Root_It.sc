// #Sireum #Logika
import org.sireum._

def sq_root(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res[Z] * Res[Z] <= n, n < (Res[Z] + 1) * (Res[Z] + 1))
  )
  var x: Z = 0
  var y: Z = n + 1
  while (x + 1 != y) {
    val measure_yx_pre = y - x
    Deduce(|- (measure_yx_pre >= 0))
    val z: Z = (x + y) / 2
    if (z * z <= n) {
      x = z
    } else {
      y = z
    }
    val measure_yx_post = y - x
    Deduce(|- (measure_yx_post < measure_yx_pre))
  }
  return x
}

@pure def sq_root_unfold(n: Z): Z = {
  var x: Z = 0
  var y: Z = n + 1
  while (x + 1 != y) {
    val z: Z = (x + y) / 2
    if (z * z <= n) {
      x = z
    } else {
      y = z
    }
  }
  return x
}

@pure def sq_root_lb(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(sq_root_unfold(n) * sq_root_unfold(n) <= n)
  )
}

@pure def sq_root_ub(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(n < (sq_root_unfold(n) + 1) * (sq_root_unfold(n) + 1))
  )
}

@pure def sq_root_unfold_term(n: Z): Z = {
  var x: Z = 0
  var y: Z = n + 1
  while (x + 1 != y) {
    val measure_yx_pre = y - x
    assert(measure_yx_pre >= 0)
    val z: Z = (x + y) / 2
    if (z * z <= n) {
      x = z
    } else {
      y = z
    }
    val measure_yx_post = y - x
    assert(measure_yx_post < measure_yx_pre)
  }
  return x
}


@pure def sq_root_lb_term(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(sq_root_unfold_term(n) * sq_root_unfold_term(n) <= n)
  )
}

@pure def sq_root_ub_term(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(n < (sq_root_unfold_term(n) + 1) * (sq_root_unfold_term(n) + 1))
  )
}
