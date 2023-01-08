//
// Clone of well-known video game about falling bricks :)
// Copyright (C) Mate Kukri, 2023
//

import libc
import sdl2

// Represents a color
struct Color(r: Int32, g: Int32, b: Int32)

// Background color of the playfield
const BACKGROUND: Color = Color(50, 50, 50)

// Colormap (the playfield indexes this)
const COLOR_INVALID : Uint8 = 0
const COLOR_CYAN    : Uint8 = 1
const COLOR_BLUE    : Uint8 = 2
const COLOR_ORANGE  : Uint8 = 3
const COLOR_YELLOW  : Uint8 = 4
const COLOR_GREEN   : Uint8 = 5
const COLOR_PURPLE  : Uint8 = 6
const COLOR_RED     : Uint8 = 7
const COLOR_GRAY    : Uint8 = 8

const COLORMAP: [9]Color = [
  Color(-1,  -1,  -1 ), // Invalid
  Color(0,   240, 241), // Cyan
  Color(0,   0,   240), // Blue
  Color(237, 161, 0  ), // Orange
  Color(240, 240, 0  ), // Yellow
  Color(0,   240, 0  ), // Green
  Color(160, 0,   241), // Purple
  Color(241, 0,   0  ), // Red
  Color(150, 150, 150)  // Gray
]

// Playfield size
const PLAYFIELD_W: Uintn = 10
const PLAYFIELD_H: Uintn = 24

// Convert a position into a playfield index
function xy_to_idx (x: Uintn, y: Uintn) -> Uintn { y * PLAYFIELD_W + x }

// Position in 2D space
struct Vec2 (x: Int32, y: Int32)

// Description of brick
struct Brick (
  // Color index
  color_idx: Uint8,
  // Width of its bounding box
  box_width: Int32,
  // Points of the piece
  points: [4]Vec2,
  // Offset of the bounding box (from the top left)
  offset: Vec2
)

/*

//
// Constructors for various brick variants
//

function create_I () -> Brick {
  Brick (
    color_idx: COLOR_CYAN,
    box_width: 4,
    points: [ Vec2(0, 1), Vec2(1, 1), Vec2(2, 1), Vec2(3, 1) ],
    offset: Vec2(0,0)
  )
}
function create_J () -> Brick {
  Brick (
    color_idx: COLOR_BLUE,
    box_width: 3,
    points: [ Vec2(0, 0), Vec2(0, 1), Vec2(1, 1), Vec2(2, 1) ],
    offset: Vec2(0,0)
  )
}
function create_L () -> Brick {
  Brick (
    color_idx: COLOR_ORANGE,
    box_width: 3,
    points: [ Vec2(0, 1), Vec2(1, 1), Vec2(2, 1), Vec2(2, 0) ],
    offset: Vec2(0,0)
  )
}
function create_O () -> Brick {
  Brick (
    color_idx: COLOR_YELLOW,
    box_width: 2,
    points: [ Vec2(0, 0), Vec2(1, 0), Vec2(0, 1), Vec2(1, 1) ],
    offset: Vec2(0,0)
  )
}
function create_S () -> Brick {
  Brick (
    color_idx: COLOR_GREEN,
    box_width: 3,
    points: [ Vec2(0, 1), Vec2(1, 1), Vec2(1, 0), Vec2(2, 0) ],
    offset: Vec2(0,0)
  )
}
function create_T () -> Brick {
  Brick (
    color_idx: COLOR_PURPLE,
    box_width: 3,
    points: [ Vec2(0, 1), Vec2(1, 1), Vec2(2, 1), Vec2(1, 0) ],
    offset: Vec2(0,0)
  )
}
function create_Z () -> Brick {
  Brick (
    color_idx: COLOR_RED,
    box_width: 3,
    points: [ Vec2(0, 0), Vec2(1, 0), Vec2(1, 1), Vec2(2, 1) ],
    offset: Vec2(0,0)
  )
}

const CTOR_CNT: Uintn = 7
const CTOR_ARR: [CTOR_CNT]Function() -> Brick =
  [ create_I, create_J, create_L, create_O, create_S, create_T, create_Z ]

function create_random() -> Brick {
  CTOR_ARR[libc::rand() % CTOR_CNT]()
}

*/

function main() -> Int32 {
  let err = sdl2::SDL_Init(sdl2::SDL_INIT_EVERYTHING) != 0;


  0
}
