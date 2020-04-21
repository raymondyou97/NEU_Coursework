import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.when;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.delete;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.get;
import static org.springframework.test.web.servlet.result.MockMvcResultHandlers.print;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.status;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonInclude.Include;
import models.ServiceQuestion;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.web.servlet.WebMvcTest;
import org.springframework.boot.test.mock.mockito.MockBean;
import org.springframework.test.context.junit4.SpringRunner;
import org.springframework.test.web.servlet.MockMvc;
import org.springframework.test.web.servlet.MvcResult;
import services.ServiceQuestionService;

@RunWith(SpringRunner.class)
@WebMvcTest(ServiceQuestionService.class)
@JsonInclude(Include.NON_NULL)
public class ServiceQuestionServiceTest {
    @Autowired
    private MockMvc mockMvc;
    @MockBean
    private ServiceQuestionService service;

    @Test
    public void testFindAllServiceQuestions() throws Exception {
        ServiceQuestion sq1 = new ServiceQuestion("question1", "type1", "choice1", null, null);
        ServiceQuestion sq2 = new ServiceQuestion("question2", "type2", "choice2", null, null);
        ServiceQuestion sq3 = new ServiceQuestion("question3", "type3", "choice3", null, null);
        List<ServiceQuestion> sqs = new ArrayList<>(Arrays.asList(sq1, sq2, sq3));

        when(service.findAllServiceQuestions()).thenReturn(sqs);
        MvcResult result = this.mockMvc.perform(get("/api/serviceQuestions")).andDo(print()).andExpect(status().isOk())
                .andReturn();

        String content = result.getResponse().getContentAsString();
        String requestResult = "[{\"id\":null,\"question\":\"question1\",\"type\":\"type1\",\"choices\":\"choice1\"},{\"id\":null,\"question\":\"question2\",\"type\":\"type2\",\"choices\":\"choice2\"},{\"id\":null,\"question\":\"question3\",\"type\":\"type3\",\"choices\":\"choice3\"}]";
        assertEquals(content, requestResult);
    }

    @Test
    public void testFindAServiceQuestions() throws Exception {
        ServiceQuestion sq1 = new ServiceQuestion("question1", "type1", "choice1", null, null);
        sq1.setId(1);
        ServiceQuestion sq2 = new ServiceQuestion("question2", "type2", "choice2", null, null);
        sq1.setId(2);
        List<ServiceQuestion> sqs = new ArrayList<>(Arrays.asList(sq1, sq2));

        when(service.findServiceQuestionById(2)).thenReturn(sq2);
        MvcResult result = this.mockMvc.perform(get("/api/serviceQuestions/2")).andDo(print())
                .andExpect(status().isOk()).andReturn();

        String content = result.getResponse().getContentAsString();
        String requestResult = "{\"id\":null,\"question\":\"question2\",\"type\":\"type2\",\"choices\":\"choice2\"}";
        assertEquals(content, requestResult);
    }

    @Test
    public void testDeleteAServiceQuestions() throws Exception {
        ServiceQuestion sq1 = new ServiceQuestion("question1", "type1", "choice1", null, null);
        sq1.setId(1);
        ServiceQuestion sq2 = new ServiceQuestion("question2", "type2", "choice2", null, null);
        sq1.setId(2);
        List<ServiceQuestion> sqs = new ArrayList<>(Arrays.asList(sq1, sq2));

        this.mockMvc.perform(delete("/api/serviceQuestions/2")).andDo(print()).andExpect(status().isOk());
    }
}