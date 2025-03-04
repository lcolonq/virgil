SDL_CFLAGS = `sdl2-config --cflags` -DVIRGIL_SDL2
SDL_LIBS = `sdl2-config --cflags --libs` -lSDL2_mixer
CC = gcc
CFLAGS+=-g -Idoomgeneric

FILENAMES = virgil_libc.c dummy.c am_map.c doomdef.c doomstat.c dstrings.c d_event.c d_items.c d_iwad.c d_loop.c d_main.c d_mode.c d_net.c f_finale.c f_wipe.c g_game.c hu_lib.c hu_stuff.c info.c i_cdmus.c i_endoom.c i_joystick.c i_scale.c i_sound.c i_system.c i_timer.c memio.c m_argv.c m_bbox.c m_cheat.c m_config.c m_controls.c m_fixed.c m_menu.c m_misc.c m_random.c p_ceilng.c p_doors.c p_enemy.c p_floor.c p_inter.c p_lights.c p_map.c p_maputl.c p_mobj.c p_plats.c p_pspr.c p_saveg.c p_setup.c p_sight.c p_spec.c p_switch.c p_telept.c p_tick.c p_user.c r_bsp.c r_data.c r_draw.c r_main.c r_plane.c r_segs.c r_sky.c r_things.c sha1.c sounds.c statdump.c st_lib.c st_stuff.c s_sound.c tables.c v_video.c wi_stuff.c w_checksum.c w_file.c w_main.c w_wad.c z_zone.c w_file_stdc.c i_input.c i_video.c doomgeneric.c
SRCS += $(addprefix doomgeneric/, $(FILENAMES))

doomsdl2: all.c wad.h
	$(CC) $(CFLAGS) $(SDL_CFLAGS) $(LDFLAGS) $< doomgeneric/doomgeneric_sdl.c -o $@ -lm -lc $(SDL_LIBS)

all_pp.c: all.c wad.h
	$(CC) $(CFLAGS) -nostdlib -nostdinc -E $< -o $@

all.c: $(SRCS)
	cat $^ >$@

wad.h: doom1.wad
	xxd -i $< >$@

clean:
	rm doomsdl2 all_pp.c all.c
