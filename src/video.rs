use sdl2::image::LoadTexture;

pub fn video() {
    let sdl = sdl2::init().expect("failed to initialize sdl2");
    let video = sdl.video().expect("failed to initialize video");
    let window = video.window("bad apple :3", 800, 600).build().expect("failed to open window");

    let mut canvas = window.into_canvas()
        .accelerated()
        .build().expect("failed to initialize canvas");

    let texture_creator = canvas.texture_creator();
    let framecount = 6574;
    let mut frames = Vec::new();
    
   
    for idx in 1..=framecount {
        frames.push(
            texture_creator.load_texture(format!("data/frames/{:0>4}.png", idx))
                .expect("failed to load texture")
        );
    }

    let mut event_pump = sdl.event_pump().expect("failed to initialize event pump");
    let mut frame = 0;
    'running: loop {
        frame = (frame + 1) % framecount;
        for event in event_pump.poll_iter() {
            match event {
                sdl2::event::Event::Quit {..} => { break 'running },
                _ => {},
            }
        }
        canvas.copy(
            &frames[frame],
            None,
            Some(sdl2::rect::Rect::new(0, 0, 480, 360)),
        ).expect("failed to draw texture");
        canvas.present();
    }
}
