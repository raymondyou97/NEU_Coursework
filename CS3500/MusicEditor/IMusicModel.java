package cs3500.music.model;

import java.util.ArrayList;
import java.util.TreeMap;

/**
 * Represents the music editor interface
 */
public interface IMusicModel<T> {

  /**
   * adds a note
   * @param note
   */
  void add(T note);

  /**
   * removes a note
   * @param note
   */
  void removeNote(T note);

  /**
   * edits a note
   * @param note represents the note to be moved
   * @param beatStart represents the new beatStart
   * @param beatEnd represents the new beatEnd
   */
  void editNote(T note, int beatStart, int beatEnd);

  /**
   * move a note
   * @param note represents the note to be moved
   * @param newKey represents the new key that the note is moving to
   * @param newPitch represents the new pitch that the note is moving to
   */
  void moveNote(T note, int newKey, int newPitch);



  /**
   * allows two music pieces to play simultaneously
   * @param musicModel another music model
   */
  void makeSimultaneous(IMusicModel<T> musicModel);

  /**
   * allows two music pieces to play consecutively
   * @param musicModel another music model
   */
  void makeConsecutive(IMusicModel<T> musicModel);

  /**
   * @return all the notes in one arrayList
   */
  ArrayList<Note> retrieveAllNotes();

  /**
   *
   * @return the notes that are playing at the current beat
   */
  ArrayList<Note> retrieveCurrentPlayingNotes(int beatStart);


  /**
   * clear all the notes in the current music piece
   */
  void clearPiece();

  /**
   *
   * @return a clone of the music
   */
  TreeMap<Integer, ArrayList<Note>> retrieveMusic();

  /**
   *
   * @return the tempo of the music
   */
  int getTempo();

  /**
   * Sets the value of the tempo
   * @param tempo
   * @throws IllegalArgumentException if tempo is negative
   */
  void setTempo(int tempo);

  /**
   * @return the integer value of the lowest pitch
   */
  int getLowestPitch();

  /**
   * @return the integer value of the highest pitch
   */
  int getHighestPitch();

  /**
   * find the end beat of the last note
   * @return duration of the music
   */
  int getDuration();

  /**
   * @return the integer value of the current beat number
   */
  int getCurrentBeat();

  /**
   * Set the current beat number
   * @param beatNum
   * @throws IllegalArgumentException if beatNum is negative or greater than the duration
   */
  void updateCurrentBeat(int beatNum);
}
