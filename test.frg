abstract sig Ship {   
   length: one Int
   partOfShip: pfunc Coordinate -> Yes   
}

sig Coordinate {
    x: one Int
    y: one Int
}

sig Destroyer extends Ship {}
sig Carrier extends Ship {}
sig Battleship extends Ship {}
sig Cruiser extends Ship {}
sig Submarine extends Ship {}

abstract sig Player {
    destroyer: one Destroyer
    carrier: one Carrier
    battleship: one Battleship
    cruiser: one Cruiser
    submarine: one Submarine
}
one sig A, B extends Player {}

pred wellFormedShips {
    all s: Ship | {
        #{c: Coordinate | s.partOfShip[c] = Yes} = s.length
        some disj c1, c2: Coordinate | {
            s.partOfShip[c1] and s.partOfShip[c2] => {
                (c1.x - c2.x < s.length and c1.y = c2.y) or
                (c1.y - c2.y < s.length and c1.x = c2.x)
            }
        }
    }
}

sig State {
    boardA: pfunc Int -> Int -> Attacked
    boardB: pfunc Int -> Int -> Attacked    
}

abstract sig Attacked {}

pred init {
    
}

pred noOverlap {}

pred move[pre: State, row: Int, col: Int, p: Player, post: State] {}

pred wellformed {
    //no overlap
    //no ship position outside of board
    //
}

pred ATurn[s: State] {}

pred BTurn[s: State] {}


pred Lengths {
    Destroyer.length = 2
    Carrier.length = 5
    Battleship.length = 4
    Cruiser.length = 3
    Submarine.length = 3
}


