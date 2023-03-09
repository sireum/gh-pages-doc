// #Sireum #Logika
import org.sireum._

@pure def pure_max(x: Z, y: Z): Z = {
  if (x < y) {
    return y
  } else {
    return x
  }
}

def max(x: Z, y: Z): Z = {
  if (x < y) {
    return y
  } else {
    return x
  }
}

val x = randomInt()
val y = randomInt()

val z = max(x, y)
Deduce(|- (z == pure_max(x, y)))