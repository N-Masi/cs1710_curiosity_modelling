#lang forge/bsl "cm" "awbmytxbhfb9ij16"

abstract sig Ship {
    // this is a set of the coordinates part of the ship
    partOfShip: pfunc Coordinate -> Yes,
    length: one Int
}

one sig Yes {}

// doing this rather than a pfunc that takes two Int
// as input allows us to count the number of Coordinates
// that have a certain property (e.g., such as being 
// part of a ship)
sig Coordinate {
    location: pfunc Int -> Int -> Yes
}

abstract sig Carrier {} // 5 coordinates long
abstract sig Battleship {} // 4 coordinates long
abstract sig Cruiser {} // 3 coordinates long
abstract sig Submarine {} // 3 coordinates long
abstract sig Destroyer {} // 2 coordinates long

// we only ever compare PlayerA's ship's partOfShip
// to boardA and likewise for B
abstract sig Player{
    carrier: one Carrier,
    battleship: one Battleship,
    cruiser: one Cruiser,
    submarine: one Submarine,
    destroyer: one Destroyer
}
one PlayerA, PlayerB extends Player{}

sig State {
    // each player needs their own board to track where
    // their opponent has attacked
    boardA: pfunc Coordinate -> Attacked,
    boardB: pfunc Coordinate -> Attacked
}

// this is again basically a set, where
// if a player has attacked a spot on a board
// the board pfuncs will return the attacked object
// and if the coordinate hasn't been attacked
// then the pfuncs will return none
one sig Attacked {}

pred init[s: State] {
    -- all board outputs are none
    -- one of each ship type per board
}

pred wellformed[s: State] {
    -- ships aren't overlapping
    -- no ship position outside the board (<0 or >10)
    -- shipLenghts pred
    -- wellformed for each ship's partOfShip
    -- wellformedShips for all ships
}

pred wellformedShips[s : Ship] {
    -- ship is the length it should be
    #{c : Coordiate | s.partOfShip[c] = Yes} = s.length
    -- ship coordinates are in a row
    some disj c1, c2: Coordinate | {
        s.partOfShip[c1] and s.partOfShip[c2] => {
            (c1.x - c2.x < s.length and c1.y = c2.y) or
            (c1.y - c2.y < s.length and c1.x = c2.x)
        }
    }
}

// sets ships lengths to the right value
pred shipLengths {
    all c : Carrier | {
        c.length = 5
    }
    all b : Battleship | {
        b.length = 4
    }
    all c : Cruiser | {
        c.length = 3
    }
    all s : Submarine | {
        s.length = 3
    }
    all d : Destroyer | {
        d.length = 2
    }
}

pred validTransition[pre: State, post: State] {
    -- for all ships, partOfShip is exactly the same
    -- only one Outcome changes on one board func
    -- the board which changes alternates between turns
    -- attack that was taken was on input ints 0<=10
}

pred gameOver[s : State] {
    all of 
}

pred noMove[pre: State, post: State] {

}

-- traces of State
run {
    -- enforce init on some start state
    -- enforce wellformed on all states
    -- enforce validTransition between states
    -- enfore gameOver on some state
    -- enfore noMove on all states after gameOver
} for 5 Int