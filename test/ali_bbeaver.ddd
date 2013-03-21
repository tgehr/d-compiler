import std.stdio;
import std.array;
import std.range;

enum Direction { L, R }

struct repeat(int Value) {
    enum head = Value;
    alias repeat!Value tail;
}

struct cons(int Head, Tail) {
    enum head = Head;
    alias Tail tail;
}

struct step(Direction d, Left, Right) {
    static if (d == Direction.L) {
        alias Left.tail left;
        alias cons!(Left.head, Right) right;

    } else static if (d == Direction.R) {
        alias cons!(Right.head, Left) left;
        alias Right.tail right;

    } else {
        static assert(false);
    }
}

struct turing_machine(TuringMachine, Left, Right,
                      State = TuringMachine.initial_state)
    if (!is (State == TuringMachine.final_state))
{
    alias TuringMachine.transition_table!(Right.head, State) transition;
    alias step!(transition.direction, Left,
                cons!(transition.symbol, Right.tail)) after;

    alias turing_machine!(TuringMachine, after.left, after.right,
                          transition.state) next;

        alias next.final_left final_left;
        alias next.final_right final_right;
}

struct turing_machine(TuringMachine, Left, Right,
                      State)
    if (is (State == TuringMachine.final_state))
{
    alias Left final_left;
    alias Right final_right;
}

struct busy_beaver {
    struct A {}
    struct B {}
    struct H {}

    struct transition_table(int Sym, State) {
        static if (Sym == 0) {
            static if (is (State == busy_beaver.A)) {
                enum symbol = 1;
                enum direction = Direction.R;
                alias B state;

            } else static if (is (State == busy_beaver.B)) {
                enum symbol = 1;
                enum direction = Direction.L;
                alias A state;

            } else {
                static assert(false);
            }

        } else static if (Sym == 1) {
            static if (is(State == busy_beaver.A)) {
                enum symbol = 1;
                enum direction = Direction.L;
                alias B state;

            } else static if (is(State == busy_beaver.B)) {
                enum symbol = 1;
                enum direction = Direction.R;
                alias H state;

            } else {
                static assert(false);
            }

        } else {
            static assert(false);
        }
    }

    alias A initial_state;
    alias H final_state;
}

struct type_list_to_vector(Cons : cons!(Head, Tail), int Head, Tail) {
    void opCall(ref int[] output) {
        output ~= Head;
        type_list_to_vector!Tail tl2v;
        tl2v(output);
    }

    static auto opCall() {
        type_list_to_vector!Cons tl2v;
        return tl2v;
    }
}

struct type_list_to_vector(Repeat : repeat!Value, int Value) {
    void opCall(ref int[] output) {
        output ~= Value;
    }
}

void main() {
    alias turing_machine!(busy_beaver, repeat!0, repeat!0) tm;

    int[] tape;
    type_list_to_vector!(tm.final_left)()(tape);

    writef(".. %s ", tape.back);
    foreach (i; retro(tape)) {
        writef("%s ", i);
    }

    tape = tape.init;
    type_list_to_vector!(tm.final_right)()(tape);
    writef("*%s* ", tape.front);
    foreach (i; tape[1 .. $]) {
        writef("%s ", i);
    }
    writefln("%s ..", tape.back);
}
