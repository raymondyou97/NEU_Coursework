package cs3500.music.model;
import java.util.ArrayList;
import java.util.TreeMap;
import cs3500.music.util.CompositionBuilder;

/**
 * Represents the music model implementation
 */
public final class MusicModel implements IMusicModel<Note> {

  TreeMap<Integer, ArrayList<Note>> music = new TreeMap<>();
  private int highestPitchValue = 0;
  private int lowestPitchValue = 1000;
  private int currentBeatNumber = 0;
  // 1 million microseconds per beat
  private int tempo = 1000000;


  /**
   * constructs a music piece
   */
  MusicModel() {
    if (lowestPitchValue < 0) {
      throw new IllegalArgumentException("Lowest pitch value cannot be negative");
    }
    if (currentBeatNumber < 0) {
      throw new IllegalArgumentException("Current beat number cannot be negative");
    }
    if (tempo < 0) {
      throw new IllegalArgumentException("Tempo cannot be negative");
    }
  }

  /**
   * Sets the value of the tempo
   * @param tempo
   * @throws IllegalArgumentException if tempo is negative
   */
  public void setTempo(int tempo) {
    if (tempo < 0) {
      throw new IllegalArgumentException("tempo can't be negative");
    }
    this.tempo = tempo;
  }

  /**
   *
   * @return the tempo of the music
   */
  @Override
  public int getTempo() {
    return this.tempo;
  }

  /**
   *
   * @return a clone of the music
   */
  public TreeMap<Integer, ArrayList<Note>> retrieveMusic() {
    TreeMap<Integer, ArrayList<Note>> temp =
            (TreeMap<Integer, ArrayList<Note>>)this.music.clone();
    return temp;
  }

  /**
   * adds a note
   * @param note
   */
  @Override
  public void add(Note note) {
    //checks if the map has an ArrayList at the given key
    if (this.music.containsKey(note.getStartBeat())) {
      // checks if the ArrayList has the same note
      if (this.music.get(note.getStartBeat()).contains(note)) {
        //replaces the note
        int indexOfNote = this.music.get(note.getStartBeat()).indexOf(note);
        this.music.get(note.getStartBeat()).set(indexOfNote, note);
      }
      else {
        //else add the note to the ArrayList
        this.music.get(note.getStartBeat()).add(note);
      }

      // updates the pitch value
      if (note.getPitchValue() > this.getHighestPitch()) {
        this.highestPitchValue = note.getPitchValue();
      }

      if (note.getPitchValue() < this.getLowestPitch()) {
        this.lowestPitchValue = note.getPitchValue();
      }
    }

    // if ArrayList does not exist in map at the given key, construct one and put it in the map
    else {
      ArrayList<Note> listOfNote = new ArrayList<>();
      listOfNote.add(note);
      this.music.put(note.getStartBeat(), listOfNote);

      // updates the pitch value in case new pitch is higher than current
      if (note.getPitchValue() > this.getHighestPitch()) {
        this.highestPitchValue = note.getPitchValue();
      }
      if (note.getPitchValue() < this.getLowestPitch()) {
        this.lowestPitchValue = note.getPitchValue();
      }
    }
  }

  /**
   * removes a note
   * @param note
   */
  @Override
  public void removeNote(Note note) {
    if (this.music.containsValue(this.music.get(note.getStartBeat()))) {
      //saves location of the key
      int noteKey = note.getStartBeat();

      //retrieves the ArrayList at the key and removes the note
      ArrayList<Note> newArray = this.music.get(note.getStartBeat());
      newArray.remove(note);

      //replaces the ArrayList with one that has removed the note
      this.music.put(noteKey, newArray);

    }
    else {
      throw new IllegalArgumentException("The note does not exist.");
    }
  }

  /**
   * @return the integer value of the highest pitch
   */
  @Override
  public int getHighestPitch() {
    return this.highestPitchValue;
  }

  /**
   * @return the integer value of the lowest pitch
   */
  @Override
  public int getLowestPitch() {
    return this.lowestPitchValue;
  }

  /**
   * find the end beat of the last note
   * @return duration of the music
   */
  @Override
  public int getDuration() {
    // if the music is empty
    if (this.music.size() == 0) {
      return 0;
    }
    else {
      int highestCurrentDuration = 0;
      ArrayList<Note> allNotes = this.retrieveAllNotes();
      for (Note note : allNotes) {
        if (note.getEndBeat() > highestCurrentDuration) {
          highestCurrentDuration = note.getEndBeat();
        }
      }
      return highestCurrentDuration;
    }
  }

  /**
   * @return the integer value of the current beat number
   */
  @Override
  public int getCurrentBeat() {
    return this.currentBeatNumber;
  }


  /**
   * Set the current beat number
   * @param beatNum
   * @throws IllegalArgumentException if beatNum is negative or greater than the duration
   */
  @Override
  public void updateCurrentBeat(int beatNum) {
    if(beatNum < 0) {
      throw new IllegalArgumentException("beatNum can't be negative");
    }
    if (beatNum > this.getDuration()) {
      throw new IllegalArgumentException("beatNum can't be larger than " +
              "duration of music piece");
    }

    this.currentBeatNumber = beatNum;
  }

  /**
   * move a note
   * @param note represents the note to be moved
   * @param newKey represents the new key that the note is moving to
   * @param newPitch represents the new pitch that the note is moving to
   */
  @Override
  public void moveNote(Note note, int newKey, int newPitch) {
    int noteDuration = note.getEndBeat() - note.getStartBeat();
    // if the note exist in the map
    if (this.music.containsValue(this.music.get(note.getStartBeat()))
            && this.music.get(note.getStartBeat()).contains(note)) {
      // if there is an arrayList constructed in the newKey already
      if (this.music.containsValue(this.music.get(newKey))) {
        this.removeNote(note);

        ArrayList<Note> list = this.music.get(newKey);
        list.set(newPitch, note);
        //replace the old arrayList with the new arrayList without the given oldNote
        this.music.put(newKey, list);
        // modify the note's beatStart, beatEnd, duration doesn't change
        note.editNoteLength(newKey, newKey + noteDuration);
      }
      else {
        // remove the old note
        this.removeNote(note);

        //makes a new list and adds the note and adds it into the TreeMap
        ArrayList<Note> listOfNote = new ArrayList<>();
        listOfNote.add(note);
        this.music.put(newKey, listOfNote);

        // changes the notes beatStart and beatEnd
        note.editNoteLength(newKey, newKey + noteDuration);
      }
    }
    else {
      throw new IllegalArgumentException("Note does not exist");
    }
  }

  /**
   * edits a note
   * @param note represents the note to be moved
   * @param beatStart represents the new beatStart
   * @param beatEnd represents the new beatEnd
   */
  @Override
  public void editNote(Note note, int beatStart, int beatEnd) {
    note.editNoteLength(beatStart, beatEnd);
  }

  /**
   * allows two music pieces to play simultaneously
   * @param musicModel another music model
   */
  @Override
  public void makeSimultaneous(IMusicModel<Note> musicModel) {

    // makes a copy of the music piece from the given interface
    ArrayList<Note> temp = musicModel.retrieveAllNotes();

    for (Note n : temp) {
      this.add(n);
    }
  }

  /**
   * allows two music pieces to play consecutively
   * @param musicModel another music model
   */
  @Override
  public void makeConsecutive(IMusicModel<Note> musicModel) {

    ArrayList<Note> listOfNoteFromModel = musicModel.retrieveAllNotes();

    for (Note n : listOfNoteFromModel) {
      n.editNoteLength(n.getStartBeat() + this.getDuration(),
              n.getEndBeat() + this.getDuration());
      this.add(n);
    }

  }

  /**
   * @return all the notes in one arrayList
   */
  @Override
  public ArrayList<Note> retrieveAllNotes() {
    ArrayList<Note> listOfNote = new ArrayList<>();
    for (int i : this.music.keySet()) {
      for (Note n : this.music.get(i)) {
        listOfNote.add(n);
      }
    }
    return listOfNote;
  }

  /**
   *
   * @return the notes that are playing at the current beat
   */
  @Override
  public ArrayList<Note> retrieveCurrentPlayingNotes(int beatStart) {
    ArrayList<Note> al = this.music.get(beatStart);
    if (al == null) {
      return new ArrayList<>();
    }
    else {
      return al;
    }
  }

  /**
   * clear all the notes in the current music piece
   */
  @Override
  public void clearPiece() {
    this.music = new TreeMap<>();
  }


  /**
   * represents a builder class for MusicModel class
   */
  public static final class Builder implements CompositionBuilder<IMusicModel<Note>> {

    private MusicModel model;

    public Builder() {
      this.model = new MusicModel();
    }

    /**
     * Constructs an actual composition, given the notes that have been added
     * @return The new composition
     */
    @Override
    public IMusicModel<Note> build() {
      return this.model;
    }


    /**
     * Sets the tempo of the piece
     * @param tempo The speed, in microseconds per beat
     * @return This builder
     */
    @Override
    public CompositionBuilder<IMusicModel<Note>> setTempo(int tempo) {
      this.model.setTempo(tempo);
      return this;
    }


    /**
     * Adds a new note to the piece
     * @param start The start time of the note, in beats
     * @param end The end time of the note, in beats
     * @param instrument The instrument number (to be interpreted by MIDI)
     * @param pitch The pitch (in the range [0, 127], where 60 represents C4,
     *              the middle-C on a piano)
     * @param volume The volume (in the range [0, 127])
     * @return
     */
    @Override
    public CompositionBuilder<IMusicModel<Note>> addNote(int start, int end, int instrument,
                                                         int pitch, int volume) {
      Note newNote = new Note(start, end, pitch / 12,
              Pitch.findPitch(pitch % 12), instrument, volume);
      this.model.add(newNote);
      return this;
    }
  }
}






