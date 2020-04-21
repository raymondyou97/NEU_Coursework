package models;

import java.util.Date;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.ManyToOne;
import javax.persistence.PrimaryKeyJoinColumn;
import javax.persistence.Table;

import com.fasterxml.jackson.annotation.JsonIgnore;

@Entity
@Table(name = "reviews")
public class Review {
  @Id
  @GeneratedValue(strategy = GenerationType.IDENTITY)
  private Integer id;
  private String title;
  private String review;
  private Integer rating;
  private Date reviewDate;
  private String reply;
  @ManyToOne
  @PrimaryKeyJoinColumn(name = "reviewer_id", referencedColumnName = "id")
  @JsonIgnore
  private User reviewer;
  @ManyToOne
  @PrimaryKeyJoinColumn(name = "reviewed_id", referencedColumnName = "id")
  @JsonIgnore
  private User reviewed;

  public Integer getId() {
    return id;
  }

  public void setId(Integer id) {
    this.id = id;
  }

  public String getTitle() {
    return title;
  }

  public void setTitle(String title) {
    this.title = title;
  }

  public String getReview() {
    return review;
  }

  public void setReview(String review) {
    this.review = review;
  }

  public User getReviewer() {
    return reviewer;
  }

  public void setReviewer(User reviewer) {
    this.reviewer = reviewer;
  }

  public User getReviewed() {
    return reviewed;
  }

  public void setReviewed(User reviewed) {
    this.reviewed = reviewed;
  }

  public Integer getRating() {
    return rating;
  }

  public void setRating(Integer rating) {
    if (rating <= 5 && rating >= 1)
      this.rating = rating;
  }

  public Date getReviewDate() {
    return reviewDate;
  }

  public void setReviewDate(Date date) {
    this.reviewDate = date;
  }

  public String getReply() {
    return reply;
  }

  public void setReply(String reply) {
    this.reply = reply;
  }
}
