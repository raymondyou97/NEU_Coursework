package repositories;

import models.ServiceQuestion;
import org.springframework.data.jpa.repository.JpaRepository;

public interface PagedServiceQuestionRepository extends JpaRepository<ServiceQuestion, Integer> {

}
