#!/bin/sh
ffmpeg -i badapple.mp4 -f lavfi -i color=gray:s=480x360 -f lavfi -i color=black:s=480x360 -f lavfi -i color=white:s=480x360 -filter_complex threshold -r 30 frames/%04d.png
