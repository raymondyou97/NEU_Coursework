package cs3500.music.model;

import java.util.Objects;

/**
 * Represents a pitch
 */
public enum Pitch {

  C("C"),
  C_Sharp("C#"),
  D("D"),
  D_Sharp("D#"),
  E("E"),
  F("F"),
  F_Sharp("F#"),
  G("G"),
  G_Sharp("G#"),
  A("A"),
  A_Sharp("A#"),
  B("B");

  private final String pitchName;

  Pitch(String pitchName) {
    this.pitchName = pitchName;
  }

  /**
   *
   * @return pitch name as a String
   */
  @Override
  public String toString() {
    return this.pitchName;
    }

  /**
   *
   * @return the pitch value
   */
  public int getPitch() {
    return this.ordinal();
  }

  /**
   * finds the corresponding pitch according to the given value
   * @param pitchValue
   * @return Pitch
   */
  public static Pitch findPitch(int pitchValue) {
    Pitch pitch;
    switch (pitchValue) {
      case 0 : pitch = Pitch.C;
        break;
      case 1 : pitch = Pitch.C_Sharp;
        break;
      case 2 : pitch = Pitch.D;
        break;
      case 3 : pitch = Pitch.D_Sharp;
        break;
      case 4 : pitch = Pitch.E;
        break;
      case 5 : pitch = Pitch.F;
        break;
      case 6 : pitch = Pitch.F_Sharp;
        break;
      case 7 : pitch = Pitch.G;
        break;
      case 8 : pitch = Pitch.G_Sharp;
        break;
      case 9 : pitch = Pitch.A;
        break;
      case 10 : pitch = Pitch.A_Sharp;
        break;
      default: pitch = Pitch.B;
        break;
    }
    return pitch;
  }
}
