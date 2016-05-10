
deprecated("a") deprecated("b") int nonNested(){ return 1; } // error

deprecated("a") deprecated int nonNested2(){ return 2; } // error

deprecated deprecated("b") int nonNested3(){ return 3; } // error
