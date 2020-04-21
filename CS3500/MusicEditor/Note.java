package cs3500.music.model;

/**
 * Represents a note
 */
public class Note {
  private int beatStart;
  private int beatEnd;
  private int pitchValue;
  private int instrument;
  private int volume;


  /**
   * default constructor
   * @param beatStart represents the start beat of the currentNote
   * @param beatEnd represents the end beat of the currentNote
   * @param octave represents the octave of the currentNote
   * @param pitch represents the pitch of the currentNote
   * @param instrument represents the instrument that plays the music
   */
  public Note(int beatStart, int beatEnd, int octave, Pitch pitch, int instrument, int volume) {
    if (beatStart < 0 || beatEnd < 0 || octave < 0 || volume < 0) {
      throw new IllegalArgumentException("Invalid currentNote: input cannot be less than 0");
    }
    this.beatStart = beatStart;
    this.beatEnd = beatEnd;
    this.pitchValue = octave * 12 + pitch.getPitch();
    this.instrument = instrument;
    this.volume = volume;
  }

  /**
   * allows the user to edit the length of the currentNote
   * @param beatStart
   * @param beatEnd
   */
  public void editNoteLength(int beatStart, int beatEnd) {
    this.beatStart = beatStart;
    this.beatEnd = beatEnd;
  }

  /**
   * checks if two notes are equal
   * @param o
   * @return
   */
  @Override
  public boolean equals(Object o) {
    if (o instanceof Note) {
      return this.beatStart == ((Note) o).beatStart &&
              this.beatEnd == ((Note) o).beatEnd &&
              this.pitchValue == ((Note) o).pitchValue &&
              this.instrument == ((Note) o).instrument &&
              this.volume == ((Note) o).volume;
    }
    else {
      return false;
    }
  }



  /**
   *
   * @return the start beat of the note
   */
  public int getStartBeat() {
    return this.beatStart;
  }

  /**
   *
   * @return the end beat of the note
   */
  public int getEndBeat() {
    return this.beatEnd;
  }

  /**
   *
   * @return the pitch value
   */
 public int getPitchValue() {
   return this.pitchValue;
 }

  /**
   *
   * @return the instrument
   */
  public int getInstrument() {
    return this.instrument;
  }

  /**
   *
   * @return the volume
   */
  public int getVolume() {
    return this.volume;
  }

  /**
   *
   * @return the hashCode
   */
  @Override
  public int hashCode() {
    int temp = 31 * (beatStart + beatEnd + volume + pitchValue + instrument);
    return temp;
  }
}