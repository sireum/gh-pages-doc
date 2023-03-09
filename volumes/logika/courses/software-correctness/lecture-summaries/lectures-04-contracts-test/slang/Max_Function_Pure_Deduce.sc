// #Sireum #Logika
import org.sireum._

@pure def pure_max(x: Z, y: Z): Z = {
  Contract(
    Requires(x > 0, y > 0),
    Ensures(Res == x | Res == y, x <= Res, y <= Res)
  )
  if (x < y) {
    return y
  } else {
    return x
  }
}

var z: Z = randomInt()

def impure_max(x: Z, y: Z) {
  Contract(
    Requires(x > 0, y > 0),
    Modifies(z),
    Ensures(z == x | z == y, x <= z, y <= z)
  )
  if (x < y) {
    z = y
  } else {
    z = x
  }
}

val x = randomInt()
assume(x > 0)
val y = randomInt()
assume(y > 0)

impure_max(x, y)

Deduce(|- (z == pure_max(x, y)))