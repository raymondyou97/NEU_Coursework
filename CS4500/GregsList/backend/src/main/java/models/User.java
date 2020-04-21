package models;

import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import javax.persistence.*;

@Entity
@Table(name = "users")
public class User {
	@Id
	@GeneratedValue(strategy = GenerationType.IDENTITY)
	private Integer id;

	private String username;
	private String password;
	private String firstName;
	private String lastName;
	private Integer zipCode;

	// additional fields for service providers
	private String title;
	private String introduction;
	private Date businessCreationDate;
	private Integer timesHired;
	private Integer employees;
	private Boolean backgroundChecked;

	// additional fields SPECIFICALLY FOR business profile
	// title = private String businessName;
	private Integer businessYearFounded;
	// employees = private Integer businessNumberOfEmployees;
	private String businessEmail;
	private String businessAddressStreet;
	private String businessAddressCity;
	private String businessAddressState;
	private String businessAddressZip;
	private String businessPaymentMethods;
	private String businessFacebookURL;
	private String businessInstagramURL;
	private String businessTwitterURL;

	@OneToMany(mappedBy = "provider")
	private List<ServiceAnswer> serviceAnswers = new ArrayList<>();
	@OneToMany(mappedBy = "reviewed")
	private List<Review> reviewsOfMe;
	@OneToMany(mappedBy = "reviewer")
	private List<Review> myReviewsOfOthers;
	@OneToMany(mappedBy = "user")
	private List<FrequentlyAskedAnswer> frequentlyAskedAnswers = new ArrayList<>();
	@ManyToMany(cascade = { CascadeType.ALL })
	@JoinTable(name = "USERS_SERVICES", joinColumns = @JoinColumn(name = "USER_ID", referencedColumnName = "ID"), inverseJoinColumns = @JoinColumn(name = "SERVICE_ID", referencedColumnName = "ID"))
	private List<Service> services = new ArrayList<>();

	public User() {
	}

	public User(Integer i, String username, String firstName, String lastName, Integer zip) {
		this.id = i;
		this.username = username;
		this.firstName = firstName;
		this.lastName = lastName;
		this.zipCode = zip;
	}

	public String getUsername() {
		return username;
	}

	public void setUsername(String username) {
		this.username = username;
	}

	public String getPassword() {
		return password;
	}

	public void setPassword(String password) {
		this.password = password;
	}

	public String getFirstName() {
		return firstName;
	}

	public void setFirstName(String firstName) {
		this.firstName = firstName;
	}

	public String getLastName() {
		return lastName;
	}

	public void setLastName(String lastName) {
		this.lastName = lastName;
	}

	public Integer getId() {
		return id;
	}

	public void setId(Integer id) {
		this.id = id;
	}

	public Integer getZipCode() {
		return this.zipCode;
	}

	public void setZipCode(Integer zip) {
		this.zipCode = zip;
	}

	public List<ServiceAnswer> getServiceAnswers() {
		return serviceAnswers;
	}

	public void setServiceAnswers(List<ServiceAnswer> serviceAnswers) {
		this.serviceAnswers = serviceAnswers;
	}

	public List<FrequentlyAskedAnswer> getFrequentlyAskedAnswers() {
		return frequentlyAskedAnswers;
	}

	public void setFrequentlyAskedAnswers(List<FrequentlyAskedAnswer> frequentlyAskedAnswers) {
		this.frequentlyAskedAnswers = frequentlyAskedAnswers;
	}

	public List<Service> getServices() {
		return services;
	}

	public void setServices(List<Service> services) {
		this.services = services;
	}

	public Integer calculateDistance(Integer pointZip) {
		return Math.abs(this.zipCode - pointZip);
	}

	public List<Review> getReviewsOfMe() {
		return reviewsOfMe;
	}

	public void setReviewsOfMe(List<Review> reviewsOfMe) {
		this.reviewsOfMe = reviewsOfMe;
	}

	public List<Review> getMyReviewsOfOthers() {
		return myReviewsOfOthers;
	}

	public void setMyReviewsOfOthers(List<Review> myReviewsOfOthers) {
		this.myReviewsOfOthers = myReviewsOfOthers;
	}

	public Integer getTimesHired() {
		return timesHired;
	}

	public void setTimesHired(Integer times) {
		this.timesHired = times;
	}

	public String getTitle() {
		return title;
	}

	public void setTitle(String title) {
		this.title = title;
	}

	public String getIntroduction() {
		return introduction;
	}

	public void setIntroduction(String intro) {
		this.introduction = intro;
	}

	public Date getBusinessCreationDate() {
		return businessCreationDate;
	}

	public void setBusinessCreationDate(Date date) {
		this.businessCreationDate = date;
	}

	public Integer getEmployees() {
		return employees;
	}

	public void setEmployees(Integer num) {
		this.employees = num;
	}

	public Boolean getBackgroundChecked() {
		return backgroundChecked;
	}

	public void setBackgroundChecked(Boolean checked) {
		this.backgroundChecked = checked;
	}

	public Integer getBusinessYearFounded() {
		return businessYearFounded;
	}

	public void setBusinessYearFounded(Integer businessYearFounded) {
		this.businessYearFounded = businessYearFounded;
	}

	public String getBusinessEmail() {
		return businessEmail;
	}

	public void setBusinessEmail(String businessEmail) {
		this.businessEmail = businessEmail;
	}

	public String getBusinessAddressStreet() {
		return businessAddressStreet;
	}

	public void setBusinessAddressStreet(String businessAddressStreet) {
		this.businessAddressStreet = businessAddressStreet;
	}

	public String getBusinessAddressCity() {
		return businessAddressCity;
	}

	public void setBusinessAddressCity(String businessAddressCity) {
		this.businessAddressCity = businessAddressCity;
	}

	public String getBusinessAddressState() {
		return businessAddressState;
	}

	public void setBusinessAddressState(String businessAddressState) {
		this.businessAddressState = businessAddressState;
	}

	public String getBusinessAddressZip() {
		return businessAddressZip;
	}

	public void setBusinessAddressZip(String businessAddressZip) {
		this.businessAddressZip = businessAddressZip;
	}

	public String getBusinessPaymentMethods() {
		return businessPaymentMethods;
	}

	public void setBusinessPaymentMethods(String businessPaymentMethods) {
		this.businessPaymentMethods = businessPaymentMethods;
	}

	public String getBusinessFacebookURL() {
		return businessFacebookURL;
	}

	public void setBusinessFacebookURL(String businessFacebookURL) {
		this.businessFacebookURL = businessFacebookURL;
	}

	public String getBusinessInstagramURL() {
		return businessInstagramURL;
	}

	public void setBusinessInstagramURL(String businessInstagramURL) {
		this.businessInstagramURL = businessInstagramURL;
	}

	public String getBusinessTwitterURL() {
		return businessTwitterURL;
	}

	public void setBusinessTwitterURL(String businessTwitterURL) {
		this.businessTwitterURL = businessTwitterURL;
	}
}