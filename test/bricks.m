//
// Clone of well-known video game about falling bricks :)
// Copyright (C) Mate Kukri, 2023
//

import libc
import sdl2

// Represents a color
struct Color(r: Uint8, g: Uint8, b: Uint8)

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

// Brick size
const BRICK_W    : Uintn = 32
const BRICK_H    : Uintn = 32

// Window size
const WINDOW_W   : Uintn = PLAYFIELD_W * BRICK_W
const WINDOW_H   : Uintn = PLAYFIELD_H * BRICK_H

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

//
// Constructors for various brick variants
//

/*
function create_I() -> Brick {
  Brick (
    color_idx: COLOR_CYAN,
    box_width: 4,
    points: [ Vec2(0,1), Vec2(1,1), Vec2(2,1), Vec2(3,1) ],
    offset: Vec2(0,0)
  )
}

function create_J() -> Brick {
  Brick (
    color_idx: COLOR_BLUE,
    box_width: 3,
    points: [ Vec2(0,0), Vec2(0,1), Vec2(1,1), Vec2(2,1) ],
    offset: Vec2(0,0)
  )
}

function create_L() -> Brick {
  Brick (
    color_idx: COLOR_ORANGE,
    box_width: 3,
    points: [ Vec2(0,1), Vec2(1,1), Vec2(2,1), Vec2(2,0) ],
    offset: Vec2(0,0)
  )
}

function create_O() -> Brick {
  Brick (
    color_idx: COLOR_YELLOW,
    box_width: 2,
    points: [ Vec2(0,0), Vec2(1,0), Vec2(0,1), Vec2(1,1) ],
    offset: Vec2(0,0)
  )
}

function create_S() -> Brick {
  Brick (
    color_idx: COLOR_GREEN,
    box_width: 3,
    points: [ Vec2(0,1), Vec2(1,1), Vec2(1,0), Vec2(2,0) ],
    offset: Vec2(0,0)
  )
}

function create_T() -> Brick {
  Brick (
    color_idx: COLOR_PURPLE,
    box_width: 3,
    points: [ Vec2(0,1), Vec2(1,1), Vec2(2,1), Vec2(1,0) ],
    offset: Vec2(0,0)
  )
}

function create_Z() -> Brick {
  Brick (
    color_idx: COLOR_RED,
    box_width: 3,
    points: [ Vec2(0,0), Vec2(1,0), Vec2(1,1), Vec2(2,1) ],
    offset: Vec2(0,0)
  )
}

function create_random() -> Brick {
  let ctors = [ create_I, create_J, create_L,
    create_O, create_S, create_T,
    create_Z ];
  let index = (libc::rand() % 7) as <Uintn>;
  ctors[index]()
}
*/

function main() -> Int32 {
  // Initialize SDL2 and SDL2_image
  if sdl2::SDL_Init(sdl2::SDL_INIT_EVERYTHING) != 0 {
    libc::fprintf(libc::stderr,
                  c"Failed to initialze SDL2: %s\n",
                  sdl2::SDL_GetError());
    return 1;
  };

  sdl2::IMG_Init(sdl2::IMG_INIT_PNG);

  // Seed random generator
  libc::srand(sdl2::SDL_GetTicks());

  // Create window
  let window = sdl2::SDL_CreateWindow(
                title: c"Bricks",
                x: sdl2::SDL_WINDOWPOS_CENTERED,
                y: sdl2::SDL_WINDOWPOS_CENTERED,
                w: WINDOW_W,
                h: WINDOW_H,
                flags: 0);

  // Create renderer
  let renderer = sdl2::SDL_CreateRenderer(window,
                                          index: -1,
                                          flags: 0);
  // Set playfield background color
  // FIXME: actually use background constant from above
  sdl2::SDL_SetRenderDrawColor(renderer, r: 50, g: 50, b: 50, a: 0);

  // Load brick texture
  let texture = sdl2::IMG_LoadTexture(renderer, c"brick.png");

  // Initialize game state
  let mut playfield: [PLAYFIELD_H * PLAYFIELD_W]Uint8 = !;

  let mut fall_interval: Uint32 = 500;
  let mut move_interval: Uint32 = 70;

  let mut prev_fall = sdl2::SDL_GetTicks();
  let mut prev_move = sdl2::SDL_GetTicks();
  let mut spawn_time = 0;

  let mut moving_left = false;
  let mut moving_right = false;
  let mut spawn_piece = false;

  //let mut brick = create_random();

  // Event loop
  loop {
    // Handle events
    let mut event = !;
    let mut quit = false;

    while sdl2::SDL_PollEvent(&event) != 0 {
      if event.type == sdl2::SDL_KEYUP {

      } else if event.type == sdl2::SDL_KEYDOWN {

      } else if event.type == sdl2::SDL_QUIT {
        quit = true;
      }
    };

    // Exit event loop
    if quit { break };

    // Draw
    sdl2::SDL_RenderClear(renderer);

    sdl2::SDL_RenderPresent(renderer);

    // Update

  };

  // Cleanup
  sdl2::SDL_DestroyRenderer(renderer);
  sdl2::SDL_DestroyWindow(window);
  sdl2::IMG_Quit();
  sdl2::SDL_Quit();
  0
}
